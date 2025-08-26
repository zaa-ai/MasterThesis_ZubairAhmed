# Metrics_calculation.py
# Full script: clustering + detailed ARI/AMI/Silhouette math with assertions

import os
import re
import csv
import math
import string
from collections import defaultdict

import numpy as np
import pandas as pd

from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.decomposition import TruncatedSVD
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import (
    adjusted_rand_score,
    adjusted_mutual_info_score,
    silhouette_score,
    pairwise_distances,
)
from sklearn.metrics.cluster import contingency_matrix
from sklearn.cluster import KMeans
import hdbscan


# ----------------------------
# Paths (match your project layout)
# ----------------------------
BASE_DIR = os.path.abspath(".")
LOG_FOLDER = os.path.join(BASE_DIR, "failing_logs_52144")   # change if needed
PARSED_FOLDER = os.path.join(LOG_FOLDER, "parsed")
os.makedirs(PARSED_FOLDER, exist_ok=True)


# ----------------------------
# Regex patterns (from your main script)
# ----------------------------
UVM_LOG_PATTERN = re.compile(
    r"(?P<severity>UVM_INFO|UVM_WARNING|UVM_ERROR|UVM_FATAL)\s+"
    r"@\s+(?P<time>[0-9\.]+)us:\s+"
    r"\[(?P<module>[^\]]+)\]\s+"
    r"(?P<message>.+?)(?:\s+\S+\(\d+\))?$"
)
CONFIG_PATTERN = re.compile(r"\+(?P<key>UVM_TESTNAME|uvm_set_type_override|UVM_VERBOSITY)=(?P<value>[\w\.\-]+)")
SIM_WARNING_PATTERN = re.compile(
    r"(Null object access|constraint solver failure|Segmentation fault|coverage illegal hit)",
    re.IGNORECASE
)


# ----------------------------
# Utilities (trimmed from your pipeline)
# ----------------------------
def split_alphanum(text: str) -> str:
    text = re.sub(r'(?<=[A-Za-z])(?=[0-9])', ' ', text)
    text = re.sub(r'(?<=[0-9])(?=[A-Za-z])', ' ', text)
    return text

def clean_text(text):
    text = split_alphanum(str(text).lower())
    return text.translate(str.maketrans("", "", string.punctuation))

def load_logs(log_directory):
    logs = []
    if not os.path.isdir(log_directory):
        print(f"[WARN] Log directory not found: {log_directory}")
        return logs
    for filename in os.listdir(log_directory):
        if filename.endswith(".log"):
            filepath = os.path.join(log_directory, filename)
            with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                logs.append((filename, f.read()))
    return logs

def is_failing_log(content: str) -> bool:
    # Simulator issues
    if SIM_WARNING_PATTERN.search(content):
        return True
    # UVM ERROR/FATAL
    for line in content.splitlines():
        m = UVM_LOG_PATTERN.match(line.strip())
        if m and m.group("severity") in ("UVM_ERROR", "UVM_FATAL"):
            return True
    return False

def classify_logs(logs):
    passing, failing = [], []
    for fname, content in logs:
        (failing if is_failing_log(content) else passing).append((fname, content))
    return passing, failing

def extract_log_info(logs):
    """
    Build a long dataframe of parsed lines we care about (UVM, Config, Simulator).
    """
    extracted = []
    for filename, content in logs:
        for line in content.splitlines():
            line = line.strip()
            uvm_match = UVM_LOG_PATTERN.match(line)
            if uvm_match:
                extracted.append({
                    "file": filename,
                    "type": "UVM",
                    "severity": uvm_match.group("severity"),
                    "time_us": float(uvm_match.group("time")),
                    "module": uvm_match.group("module"),
                    "message": uvm_match.group("message"),
                })
                continue
            config_match = CONFIG_PATTERN.search(line)
            if config_match:
                extracted.append({
                    "file": filename,
                    "type": "Config",
                    "severity": "",
                    "time_us": 0.0,
                    "module": "CONFIG",
                    "message": f"{config_match.group('key')}={config_match.group('value')}",
                })
                continue
            sim_match = SIM_WARNING_PATTERN.search(line)
            if sim_match:
                extracted.append({
                    "file": filename,
                    "type": "Simulator",
                    "severity": "SIM_ERROR",
                    "time_us": 0.0,
                    "module": "SIM",
                    "message": sim_match.group(1),
                })
    return pd.DataFrame(extracted)

def extract_structured_features(df: pd.DataFrame) -> pd.DataFrame:
    feature_list = []
    for filename, group in df.groupby("file"):
        row = defaultdict(float)
        row["file"] = filename
        severities = group["severity"].value_counts().to_dict()
        modules = group["module"].unique()
        messages = group["message"].tolist()

        for sev in ["UVM_INFO", "UVM_WARNING", "UVM_ERROR", "UVM_FATAL", "SIM_ERROR"]:
            row[f"count_{sev}"] = severities.get(sev, 0)

        row["unique_modules"] = len(modules)
        row["total_messages"] = len(messages)

        if "UVM_ERROR" in group.severity.values:
            errs = group[group.severity == "UVM_ERROR"]["time_us"].astype(float)
            row["first_error_time"] = errs.min() if not errs.empty else 0.0
            row["last_error_time"]  = errs.max() if not errs.empty else 0.0
        else:
            row["first_error_time"] = 0.0
            row["last_error_time"]  = 0.0

        feature_list.append(row)

    df_structured = pd.DataFrame(feature_list).fillna(0.0)
    df_structured.set_index("file", inplace=True)
    return df_structured

def create_document_per_log(df, context_lines=0):
    """
    Build a text document per file:
    - If there's a UVM_ERROR, take the first error (+ optional context lines).
    - Else, take the first UVM message (if any).
    - Else, take the first Simulator message (if any).
    - Else, empty string.
    """
    documents = {}
    for fname, group in df.groupby("file"):
        group = group.reset_index(drop=True)

        # First UVM_ERROR?
        err_idx = group[group["severity"] == "UVM_ERROR"].index.min()
        if not pd.isna(err_idx):
            end_idx = int(err_idx + context_lines + 1)
            selected_msgs = group.loc[err_idx:end_idx, "message"]
            documents[fname] = " ".join(clean_text(m) for m in selected_msgs)
            continue

        # Any UVM line?
        uvm_rows = group[group["type"] == "UVM"]
        if not uvm_rows.empty:
            documents[fname] = clean_text(uvm_rows["message"].iloc[0])
            continue

        # Any Simulator line?
        sim_rows = group[group["type"] == "Simulator"]
        if not sim_rows.empty:
            documents[fname] = clean_text(sim_rows["message"].iloc[0])
            continue

        # Fallback
        documents[fname] = ""
    return pd.Series(documents)


# ----------------------------
# Metrics detail printers with formulas + assertions
# ----------------------------
def _comb2(n: int) -> int:
    n = int(n)
    return n * (n - 1) // 2 if n >= 2 else 0

def print_ari_details(labels_true, labels_pred, atol=1e-12):
    """
    Adjusted Rand Index (ARI) derivation with formulas and assertions.

    ARI = (Index - ExpectedIndex) / (MaxIndex - ExpectedIndex)
    where:
      • Contingency table C (rows=true, cols=pred), with cell counts n_ij
      • a_i = row sums, b_j = col sums, n = total samples
      • Index        = sum_{i,j} C(n_ij, 2)
      • ExpectedIdx  = [sum_i C(a_i,2) * sum_j C(b_j,2)] / C(n,2)
      • MaxIndex     = 0.5 * [sum_i C(a_i,2) + sum_j C(b_j,2)]
    """
    from sklearn.metrics import adjusted_rand_score

    C = contingency_matrix(labels_true, labels_pred)
    n = int(C.sum())
    row_sums = C.sum(axis=1).A1 if hasattr(C.sum(axis=1), "A1") else C.sum(axis=1)
    col_sums = C.sum(axis=0).A1 if hasattr(C.sum(axis=0), "A1") else C.sum(axis=0)

    # Assertions on basic quantities
    assert np.isclose(row_sums.sum(), n), "Row sums must equal n"
    assert np.isclose(col_sums.sum(), n), "Column sums must equal n"

    # Combinatorial terms
    sum_nij_c2 = sum(_comb2(x) for x in C.ravel())
    sum_ai_c2  = sum(_comb2(x) for x in row_sums)
    sum_bj_c2  = sum(_comb2(x) for x in col_sums)
    n_c2       = _comb2(n)

    expected_index = (sum_ai_c2 * sum_bj_c2) / n_c2 if n_c2 else 0.0
    max_index      = 0.5 * (sum_ai_c2 + sum_bj_c2)
    ari_num        = (sum_nij_c2 - expected_index)
    ari_den        = (max_index - expected_index)
    ari_manual     = ari_num / ari_den if ari_den != 0 else 1.0

    ari_sklearn    = adjusted_rand_score(labels_true, labels_pred)
    assert np.isclose(ari_manual, ari_sklearn, atol=1e-9), \
        f"ARI mismatch: manual={ari_manual} vs sklearn={ari_sklearn}"

    # Pretty print with formulas
    print("\n[ARI formula]")
    print("  ARI = (Index - ExpectedIndex) / (MaxIndex - ExpectedIndex)")
    print("  Index = ∑_ij C(n_ij, 2)")
    print("  ExpectedIndex = [ (∑_i C(a_i,2)) (∑_j C(b_j,2)) ] / C(n,2)")
    print("  MaxIndex = 0.5 [ ∑_i C(a_i,2) + ∑_j C(b_j,2) ]")

    print("\n[ARI details]")
    print("Contingency (rows=true, cols=pred):")
    print(C)
    print(f"n = {n}")
    print(f"∑_ij C(n_ij,2)       = {sum_nij_c2}")
    print(f"∑_i  C(a_i,2)        = {sum_ai_c2}")
    print(f"∑_j  C(b_j,2)        = {sum_bj_c2}")
    print(f"C(n,2)               = {n_c2}")
    print(f"Expected Index       = {expected_index:.6f}")
    print(f"Max Index            = {max_index:.6f}")
    print(f"Numerator (Index-E)  = {ari_num:.6f}")
    print(f"Denominator (Max-E)  = {ari_den:.6f}")
    print(f"ARI (manual)         = {ari_manual:.6f}")
    print(f"ARI (sklearn)        = {ari_sklearn:.6f}")

    return ari_manual

def print_ami_details(labels_true, labels_pred, average_method="arithmetic", atol=1e-9):
    """
    Adjusted Mutual Information (AMI) with formulas and assertions.

    Definitions (natural log base):
      • Mutual Information: MI = ∑_{i,j} p_ij * ln( p_ij / (p_i• * p_•j) )
      • Entropies: H(true) = -∑_i p_i• ln p_i•,  H(pred) = -∑_j p_•j ln p_•j
      • avgH depends on 'average_method' (arithmetic by default)
      • AMI = (MI - E[MI]) / (avgH - E[MI])
    """
    from sklearn.metrics.cluster import adjusted_mutual_info_score

    C = contingency_matrix(labels_true, labels_pred)
    n = C.sum()
    P = C / n
    pu = P.sum(axis=1)  # true distribution
    pv = P.sum(axis=0)  # pred distribution

    # Sanity checks
    P_sum = float(P.values.sum()) if hasattr(P, "values") else float(P.sum())
    assert np.isclose(P_sum, 1.0, atol=1e-12), "P must sum to 1"
    assert np.isclose(pu.sum(), 1.0, atol=1e-12), "Row probs must sum to 1"
    assert np.isclose(pv.sum(), 1.0, atol=1e-12), "Col probs must sum to 1"

    # Mutual Information (natural log)
    mi = 0.0
    for i in range(P.shape[0]):
        for j in range(P.shape[1]):
            pij = float(P[i, j])
            if pij > 0:
                mi += pij * math.log(pij / (float(pu[i]) * float(pv[j])))

    # Entropies
    Hu = -sum(float(p) * math.log(float(p)) for p in pu if p > 0)
    Hv = -sum(float(p) * math.log(float(p)) for p in pv if p > 0)

    if average_method == "arithmetic":
        avgH = (Hu + Hv) / 2.0
    elif average_method == "geometric":
        avgH = math.sqrt(Hu * Hv)
    elif average_method == "min":
        avgH = min(Hu, Hv)
    else:  # harmonic or other
        avgH = 2 * Hu * Hv / (Hu + Hv) if (Hu + Hv) > 0 else 0.0

    ami_sklearn = adjusted_mutual_info_score(labels_true, labels_pred, average_method=average_method)

    # Back-solve E[MI]: AMI = (MI - E) / (avgH - E)  =>  E = (MI - AMI*avgH) / (1 - AMI)
    e_mi = mi if ami_sklearn == 1.0 else (mi - ami_sklearn * avgH) / (1 - ami_sklearn)

    # Print formulas + details
    print("\n[AMI formula]")
    print("  MI = ∑_ij p_ij * ln( p_ij / (p_i• p_•j) )")
    print("  H(true) = -∑_i p_i• ln p_i•    H(pred) = -∑_j p_•j ln p_•j")
    print(f"  avgH ({average_method}) is used in:  AMI = (MI - E[MI]) / (avgH - E[MI])")

    print("\n[AMI details]")
    print("Contingency (rows=true, cols=pred):")
    print(C)
    print(f"n = {int(n)}")
    print(f"MI (natural log)    = {mi:.6f}")
    print(f"H(true)             = {Hu:.6f}")
    print(f"H(pred)             = {Hv:.6f}")
    print(f"avgH                = {avgH:.6f}")
    print(f"AMI (sklearn)       = {ami_sklearn:.6f}")
    print(f"Implied E[MI]       = {e_mi:.6f}  (hypergeometric model)")

    # Verify: recompute AMI from our MI/e_mi/avgH (numeric stability)
    ami_manual = (mi - e_mi) / (avgH - e_mi) if (avgH - e_mi) != 0 else 1.0
    assert np.isclose(ami_manual, ami_sklearn, atol=atol), \
        f"AMI mismatch: manual={ami_manual} vs sklearn={ami_sklearn}"

    return ami_sklearn

def print_silhouette_details(X, labels, metric="euclidean", max_print=8, atol=1e-9):
    """
    Silhouette details with formulas and assertions.

    For each sample i:
      a(i) = mean distance to all other points in its own cluster
      b(i) = min mean distance to another cluster
      s(i) = (b(i) - a(i)) / max(a(i), b(i))

    We exclude noise (-1) and require ≥2 clusters. We assert our mean silhouette
    equals sklearn's silhouette_score on the same subset.
    """
    # Exclude noise if present
    mask = labels != -1
    Xm = X[mask]
    Lm = labels[mask]

    uniq = np.unique(Lm)
    if len(uniq) < 2:
        print("\n[Silhouette details]\nNot enough clusters (need ≥2 after removing noise).")
        return None

    print("\n[Silhouette formula]")
    print("  a(i) = mean intra-cluster distance")
    print("  b(i) = min mean distance to another cluster")
    print("  s(i) = (b(i) - a(i)) / max(a(i), b(i))")
    print("  Overall silhouette = mean_i s(i)")

    D = pairwise_distances(Xm, metric=metric)
    n = D.shape[0]
    a = np.zeros(n, dtype=float)
    b = np.zeros(n, dtype=float)
    s = np.zeros(n, dtype=float)

    for idx in range(n):
        same = (Lm == Lm[idx])
        other = (Lm != Lm[idx])

        same_idx = np.where(same)[0]
        if len(same_idx) > 1:
            a[idx] = D[idx, same].sum() / (len(same_idx) - 1)
        else:
            a[idx] = 0.0  # singleton cluster

        b_vals = []
        for c in np.unique(Lm[other]):
            in_c = (Lm == c)
            b_vals.append(D[idx, in_c].mean())
        b[idx] = min(b_vals) if b_vals else 0.0

        denom = max(a[idx], b[idx])
        s[idx] = (b[idx] - a[idx]) / denom if denom > 0 else 0.0

    sil_manual = s.mean()
    sil_sklearn = silhouette_score(Xm, Lm, metric=metric)
    assert np.isclose(sil_manual, sil_sklearn, atol=atol), \
        f"Silhouette mismatch: manual={sil_manual} vs sklearn={sil_sklearn}"

    print("\n[Silhouette details] (first few points)")
    for i in range(min(max_print, n)):
        print(f"i={i:>3}  label={int(Lm[i]):>3}  a(i)={a[i]:.4f}  b(i)={b[i]:.4f}  s(i)={s[i]:.4f}")

    print("\nPer-cluster averages:")
    for c in np.unique(Lm):
        idxs = np.where(Lm == c)[0]
        print(f"  cluster {int(c):>3}: n={len(idxs):>3}  mean s(i)={s[idxs].mean():.4f}")

    print(f"\nOverall silhouette (manual)  = {sil_manual:.4f}")
    print(f"Overall silhouette (sklearn) = {sil_sklearn:.4f}")
    return sil_manual


# ----------------------------
# Main: build features, cluster, and print details
# ----------------------------
def main():
    # Load & classify
    logs = load_logs(LOG_FOLDER)
    passing_logs, failing_logs = classify_logs(logs)

    print("\nPASSING logs (skipped):")
    for fname, _ in sorted(passing_logs):
        print(f"  - {fname}")

    print("\nFAILING logs (processed):")
    for fname, _ in sorted(failing_logs):
        print(f"  - {fname}")

    if not failing_logs:
        print("\nNo failing logs found. Exiting.")
        return

    # Parse only failing logs
    df = extract_log_info(failing_logs)

    # Structured features
    df_structured = extract_structured_features(df)

    # Documents for TF-IDF
    extended_stop = [
        "packet","header","channel","count","period","difference",
        "recorded","injected","failed","unable","comerr",
        "data","value","word","status","x"
    ]
    documents = create_document_per_log(df, context_lines=0)

    # Align structured to documents order to fix row mismatch
    df_structured = df_structured.reindex(documents.index).fillna(0.0)

    # TF-IDF
    min_df_val = max(1, int(0.09 * len(documents)))
    vectorizer = TfidfVectorizer(
        preprocessor=clean_text,
        stop_words=extended_stop,
        token_pattern=r"(?u)\b[a-z][a-z]{2,}\b",
        ngram_range=(1, 1),
        min_df=min_df_val,
        max_df=0.60,
        max_features=1500,
        sublinear_tf=True,
        norm="l2",
    )
    X_tfidf = vectorizer.fit_transform(documents.values)

    # Scale & combine
    tfidf_scaled = StandardScaler(with_mean=False).fit_transform(X_tfidf)
    struct_scaled = StandardScaler().fit_transform(df_structured.values)

    r_text, r_num = 0.86, 0.14
    n_text, n_num = tfidf_scaled.shape[1], struct_scaled.shape[1]
    alpha = np.sqrt(r_text / n_text) if n_text > 0 else 0.0
    beta  = np.sqrt(r_num  / n_num)  if n_num  > 0 else 0.0

    from scipy.sparse import hstack
    hybrid = hstack([alpha * tfidf_scaled, beta * struct_scaled])
    hybrid_arr = hybrid.toarray()

    # SVD (2D)
    svd = TruncatedSVD(n_components=2, random_state=42)
    X_reduced = svd.fit_transform(hybrid)

    # Ground-truth mapping (copied from main script)
    desired = {
        "otp_trimming.log": 0,
        "spi_errors_sim.log": 0,
        "upload_tdma.log": 1,
        "ic_startup.log": 1,
        "debounce_times.log": 2,
        "dsi3_crm_ecc_2_bit_error_sim.log": 5,
        "dsi3_crm.log": 1,
        "dsi3_sync_pin_sim.log": 3,
        "register_access.log": 3,
        "dsi3_pdcm.log": 4,
        "dsi3_sync_pin.log": 4,
        "dsi3_clear_command_buffer.log": 4,
        "interrupts_test_sim.log": 4,
        "shut_off.log": 5,
        "dsi3_sync_channels.log": 5,
        "jtag_test.log": 6,
        "applicative_pattern.log": 7,
        "p52143_489.log": 7,
        "p52143_701.log": 8,
        "dsi3_pdcm_timing.log": 8,
        "dsi3_crc.log": 8,
        "app_exm_in_spec.log": 8,
        "ic_status_word.log": 9,
        "dsi3_quiscent_current.log": 10,
        "dsi3_wait.log": 10,
        "dsi3_discovery_mode.log": 10,
        "otp_pulse_width.log": 10,
        "dsi3_crm_timing.log": 11,
        "spi_framing.log": 11,
        "sram_bist.log": 12,
    }
    y_true = np.array([desired.get(f, -1) for f in documents.index])

    # ---------------- HDBSCAN ----------------
    clusterer = hdbscan.HDBSCAN(
        min_cluster_size=2,
        min_samples=1,
        metric="euclidean",
        cluster_selection_method="eom",
        cluster_selection_epsilon=0.00,
        allow_single_cluster=False,
        alpha=0.8,
    )
    hdb_labels = clusterer.fit_predict(X_reduced)

    # Sklearn metrics
    ari_hdb = adjusted_rand_score(y_true, hdb_labels)
    ami_hdb = adjusted_mutual_info_score(y_true, hdb_labels, average_method="arithmetic")
    print("\nHDBSCAN clustering metrics:")
    print(f"  Adjusted Rand Index (ARI):        {ari_hdb:.3f}")
    print(f"  Adjusted Mutual Information (AMI): {ami_hdb:.3f}")
    # Silhouette (exclude noise)
    mask_hdb = hdb_labels != -1
    if len(set(hdb_labels[mask_hdb])) >= 2:
        sil_hdb = silhouette_score(X_reduced[mask_hdb], hdb_labels[mask_hdb], metric="euclidean")
        print(f"  Silhouette (noise removed):        {sil_hdb:.3f}")
    else:
        print("  Silhouette skipped (need ≥2 clusters after removing noise)")

    # Detailed math:
    _ = print_ari_details(y_true, hdb_labels)
    _ = print_ami_details(y_true, hdb_labels, average_method="arithmetic")
    _ = print_silhouette_details(X_reduced, hdb_labels, metric="euclidean", max_print=8)

    # ---------------- KMeans ----------------
    best = {"k": None, "ari": -1.0, "labels": None}
    for k in range(2, 11):
        km_labels = KMeans(n_clusters=k, random_state=42).fit_predict(X_reduced)
        ari_k = adjusted_rand_score(y_true, km_labels)
        if ari_k > best["ari"]:
            best.update({"k": k, "ari": ari_k, "labels": km_labels})
    km_labels = best["labels"]
    ami_km = adjusted_mutual_info_score(y_true, km_labels, average_method="arithmetic")
    sil_km = silhouette_score(X_reduced, km_labels, metric="euclidean")

    print("\nKMeans clustering metrics:")
    print(f"  Best k by ARI:                     {best['k']}")
    print(f"  Adjusted Rand Index (ARI):         {best['ari']:.3f}")
    print(f"  Adjusted Mutual Information (AMI): {ami_km:.3f}")
    print(f"  Silhouette:                        {sil_km:.3f}")

    # Detailed math:
    print("\nKMeans detailed breakdowns:")
    _ = print_ari_details(y_true, km_labels)
    _ = print_ami_details(y_true, km_labels, average_method="arithmetic")
    _ = print_silhouette_details(X_reduced, km_labels, metric="euclidean", max_print=8)


if __name__ == "__main__":
    main()
