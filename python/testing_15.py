import os
import re
import csv
import pandas as pd
import numpy as np
import string
import hdbscan
from collections import defaultdict
from sklearn.feature_extraction.text import TfidfVectorizer, CountVectorizer
from sklearn.decomposition import TruncatedSVD
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import adjusted_rand_score, adjusted_mutual_info_score, silhouette_score
from sklearn.metrics.cluster import contingency_matrix  # <-- added for PPV
import matplotlib.pyplot as plt
from scipy.sparse import hstack
from sklearn.cluster import KMeans
from sklearn.neighbors import NearestNeighbors

# Paths
BASE_DIR = os.path.abspath(".")
LOG_FOLDER = os.path.join(BASE_DIR, "failing_logs_52144")
PARSED_FOLDER = os.path.join(LOG_FOLDER, "parsed")
os.makedirs(PARSED_FOLDER, exist_ok=True)

STRUCTURED_LOG_FILE   = os.path.join(PARSED_FOLDER, "uvm_log_structured.csv")
TFIDF_FEATURES_FILE   = os.path.join(PARSED_FOLDER, "tfidf_features.npy")
STRUCTURED_FEATURES_FILE = os.path.join(PARSED_FOLDER, "structured_features.npy")
HYBRID_FEATURES_FILE  = os.path.join(PARSED_FOLDER, "hybrid_features.npy")
CLUSTER_LOG_FILE      = os.path.join(PARSED_FOLDER, "logs_clusters.csv")

# Regex
UVM_LOG_PATTERN = re.compile(
    r"(?P<severity>UVM_INFO|UVM_WARNING|UVM_ERROR|UVM_FATAL)\s+"
    r"@\s+(?P<time>[0-9\.]+)us:\s+"
    r"\[(?P<module>[^\]]+)\]\s+"
    r"(?P<message>.+?)(?:\s+\S+\(\d+\))?$"
)
CONFIG_PATTERN = re.compile(r"\+(?P<key>UVM_TESTNAME|uvm_set_type_override|UVM_VERBOSITY)=(?P<value>[\w\.\-]+)")
SIM_WARNING_PATTERN = re.compile(
    r"(Null object access|constraint solver failure|Segmentation fault|coverage illegal hit)", re.IGNORECASE
)

# ---------------------------
# Utilities
# ---------------------------

def split_alphanum(text: str) -> str:
    text = re.sub(r'(?<=[A-Za-z])(?=[0-9])', ' ', text)
    text = re.sub(r'(?<=[0-9])(?=[A-Za-z])', ' ', text)
    return text

def clean_text(text):
    text = split_alphanum(str(text).lower())
    return text.translate(str.maketrans("", "", string.punctuation))

def load_logs(log_directory):
    logs = []
    for filename in os.listdir(log_directory):
        if filename.endswith(".log"):
            filepath = os.path.join(log_directory, filename)
            with open(filepath, 'r', encoding='utf-8', errors='ignore') as file:
                content = file.read()
                logs.append((filename, content))
    return logs

def is_failing_log(content: str) -> bool:
    # Simulator-level fatal/warning patterns
    if SIM_WARNING_PATTERN.search(content):
        return True
    # Any UVM_ERROR/FATAL lines?
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

def save_classification(passing, failing, out_csv):
    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["file", "status"])
        for fname, _ in sorted(passing):
            w.writerow([fname, "PASS"])
        for fname, _ in sorted(failing):
            w.writerow([fname, "FAIL"])

# Extract structured log lines
def extract_log_info(logs):
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
                    "message": uvm_match.group("message")
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
                    "message": f"{config_match.group('key')}={config_match.group('value')}"
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
                    "message": sim_match.group(1)
                })
    return pd.DataFrame(extracted)

# Structured numeric features
def extract_structured_features(df):
    feature_list = []
    grouped = df.groupby("file")
    for filename, group in grouped:
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
            e = group[group.severity == "UVM_ERROR"]["time_us"].astype(float)
            row["first_error_time"] = e.min() if not e.empty else 0.0
            row["last_error_time"]  = e.max() if not e.empty else 0.0
        else:
            row["first_error_time"] = 0.0
            row["last_error_time"]  = 0.0

        feature_list.append(row)
    df_structured = pd.DataFrame(feature_list).fillna(0.0)
    df_structured.set_index("file", inplace=True)
    np.save(STRUCTURED_FEATURES_FILE, df_structured.values)
    return df_structured

# Text document creation per log file (robust: always builds a doc per file)
def create_document_per_log(df, context_lines=0):
    """
    For each file:
      1) If there is a UVM_ERROR: take first error (+ optional context lines).
      2) Else if there is any UVM line: take first UVM message.
      3) Else if there is any Simulator line: take first SIM message.
      4) Else: empty string.
    """
    documents = {}
    for filename, group in df.groupby("file"):
        group = group.reset_index(drop=True)

        first_error_idx = group[group["severity"] == "UVM_ERROR"].index.min()
        if not pd.isna(first_error_idx):
            end_idx = int(first_error_idx + context_lines + 1)
            selected_msgs = group.loc[first_error_idx:end_idx, "message"]
            doc = " ".join(clean_text(msg) for msg in selected_msgs)
            documents[filename] = doc
            continue

        uvm_rows = group[group["type"] == "UVM"]
        if not uvm_rows.empty:
            documents[filename] = clean_text(uvm_rows["message"].iloc[0])
            continue

        sim_rows = group[group["type"] == "Simulator"]
        if not sim_rows.empty:
            documents[filename] = clean_text(sim_rows["message"].iloc[0])
            continue

        documents[filename] = ""
    return pd.Series(documents)

# ---------------------------
# Automatic, corpus-learned stopwords
# ---------------------------

def learn_stopwords(
    docs,
    token_pattern=r"(?u)\b[a-z][a-z]{2,}\b",  # match the TF-IDF token rule (3+ letters)
    df_ratio_thresh=0.80,                     # terms appearing in ≥80% of docs
    ent_thresh=0.90,                          # normalized entropy ≥ 0.90
    var_quantile=0.10,                        # bottom 10% by variance
    max_stopwords=None                        # optional cap (e.g., 500) or None
):
    """
    Learn corpus-specific stopwords each run (no hardcoding).
    Heuristics:
      • High DF ratio (very common)
      • High normalized entropy across docs (uninformative spread)
      • Very low variance across docs (no contrast)
    """
    n_docs = len(docs)
    if n_docs == 0:
        return set()

    cv = CountVectorizer(token_pattern=token_pattern)
    X = cv.fit_transform(docs)  # (n_docs, n_terms)
    terms = np.array(cv.get_feature_names_out())
    counts = X.toarray().astype(float)

    # DF ratio
    df = (counts > 0).sum(axis=0)
    df_ratio = df / float(n_docs)

    # Normalized entropy across docs for each term
    col_sums = counts.sum(axis=0)
    col_sums[col_sums == 0] = 1.0
    P = counts / col_sums  # each column sums to 1
    with np.errstate(divide='ignore'):
        logP = np.where(P > 0, np.log(P), 0.0)
    ent = -(P * logP).sum(axis=0)
    ent_norm = ent / (np.log(n_docs) if n_docs > 1 else 1.0)

    # Variance across docs
    var = counts.var(axis=0)
    var_cut = np.quantile(var, var_quantile) if n_docs > 2 else 0.0

    candidates = (
        (df_ratio >= df_ratio_thresh) |
        (ent_norm >= ent_thresh) |
        (var <= var_cut)
    )
    stop_terms = terms[candidates]

    # Optional cap: keep worst offenders by DF first, then entropy
    if max_stopwords is not None and len(stop_terms) > max_stopwords:
        idx = np.where(candidates)[0]
        order = np.lexsort((-ent_norm[idx], -df_ratio[idx]))  # DF desc, then entropy desc
        idx_sorted = idx[order]
        stop_terms = terms[idx_sorted[:max_stopwords]]

    learned = set(stop_terms.tolist())

    # Guardrail: avoid over-pruning
    if len(learned) > 0.8 * len(terms):
        topN = int(0.5 * len(terms))
        idx_sorted = np.argsort(-df_ratio)  # by DF desc
        learned = set(terms[idx_sorted[:topN]].tolist())

    # Visibility
    print("\n[Auto stopwords] Summary")
    print(f"  docs: {n_docs}, vocab: {len(terms)}")
    print(f"  selected stopwords: {len(learned)} "
          f"(df≥{df_ratio_thresh:.2f} or entropy≥{ent_thresh:.2f} or var≤{var_cut:.4g})")
    preview = sorted(list(learned))[:30]
    if preview:
        print("  preview:", preview)

    return learned

# ---------------------------
# PPV helpers
# ---------------------------

def ppv_by_pred_bin(y_true, y_pred, exclude_pred_labels=None):
    """
    Compute PPV per predicted cluster (bin) and macro-PPV.
    PPV for a bin c: max count in column c / column sum c
    exclude_pred_labels: iterable of predicted labels to ignore (e.g., {-1} for HDBSCAN noise)
    Returns: (rows: list of dicts), macro_ppv
    """
    exclude_pred_labels = set(exclude_pred_labels or [])
    # Get stable label orders used by contingency_matrix
    true_labels = np.unique(y_true)
    pred_labels = np.unique(y_pred)

    C = contingency_matrix(y_true, y_pred)

    rows = []
    ppvs = []

    for j, pred_lbl in enumerate(pred_labels):
        if pred_lbl in exclude_pred_labels:
            continue
        col = C[:, j]
        total = int(col.sum())
        if total == 0:
            continue
        hit = int(col.max())
        miss = total - hit
        ppv = hit / total
        hit_true_lbl = int(true_labels[col.argmax()]) if col.argmax() < len(true_labels) else None
        rows.append({
            "pred_bin": int(pred_lbl),
            "hit_true_label": hit_true_lbl,
            "hit": hit,
            "miss": miss,
            "total": total,
            "ppv": ppv
        })
        ppvs.append(ppv)

    macro_ppv = float(np.mean(ppvs)) if ppvs else 0.0
    return rows, macro_ppv

def micro_ppv_from_rows(ppv_rows):
    """Micro-PPV = sum hits / sum totals (size-weighted)."""
    hits = sum(r["hit"] for r in ppv_rows)
    totals = sum(r["total"] for r in ppv_rows)
    return hits / totals if totals > 0 else 0.0

# ---------------------------
# Main
# ---------------------------

def main():
    logs = load_logs(LOG_FOLDER)

    # Classify pass/fail
    passing_logs, failing_logs = classify_logs(logs)

    print("\nPASSING logs (skipped from clustering):")
    for fname, _ in sorted(passing_logs):
        print(f"  - {fname}")

    print("\nFAILING logs (processed further):")
    for fname, _ in sorted(failing_logs):
        print(f"  - {fname}")

    # Save manifest
    class_csv = os.path.join(PARSED_FOLDER, "log_classification.csv")
    save_classification(passing_logs, failing_logs, class_csv)
    print(f"\nSaved classification to {class_csv}")

    if not failing_logs:
        print("\nNo failing logs found. Exiting without clustering.")
        return

    # Parse only failing logs
    df = extract_log_info(failing_logs)
    df.to_csv(STRUCTURED_LOG_FILE, index=False)
    print(f"Saved structured log entries to {STRUCTURED_LOG_FILE}")

    # Structured numeric features
    df_structured = extract_structured_features(df)
    print(f"Saved structured numeric features to {STRUCTURED_FEATURES_FILE}")

    # Build documents (per-file text)
    documents = create_document_per_log(df, context_lines=0)

    # Align structured features to document index to guarantee row match
    df_structured = df_structured.reindex(documents.index).fillna(0.0)

    # ===== Auto-learn stopwords from current corpus =====
    auto_stop = learn_stopwords(
        list(documents.values),
        token_pattern=r"(?u)\b[a-z][a-z]{2,}\b",
        df_ratio_thresh=0.80,
        ent_thresh=0.90,
        var_quantile=0.10,
        max_stopwords=None
    )
    stop_path = os.path.join(PARSED_FOLDER, "auto_stopwords.txt")
    with open(stop_path, "w", encoding="utf-8") as f:
        for t in sorted(auto_stop):
            f.write(t + "\n")
    print(f"Saved learned stopwords → {stop_path}")

    # TF-IDF Features using learned stopwords
    min_df_val = max(1, int(0.09 * len(documents)))
    vectorizer = TfidfVectorizer(
        preprocessor=clean_text,
        stop_words=list(auto_stop),  # set -> list
        token_pattern=r"(?u)\b[a-z][a-z]{2,}\b",
        ngram_range=(1,1),
        min_df=min_df_val,
        max_df=0.60,
        max_features=1500,
        sublinear_tf=True,
        norm="l2"
    )
    X_tfidf = vectorizer.fit_transform(documents.values)

    # Print out vectorizer parameters (visibility)
    print("\nTF-IDF Vectorizer parameters actually used:")
    for param, val in vectorizer.get_params().items():
        print(f"  {param}: {val}")

    # Save TF-IDF features
    np.save(TFIDF_FEATURES_FILE, X_tfidf.toarray())
    print(f" Saved TF-IDF features to {TFIDF_FEATURES_FILE}")
    tfidf_df = pd.DataFrame(X_tfidf.toarray(), index=documents.index, columns=vectorizer.get_feature_names_out())
    tfidf_df.to_csv(os.path.join(PARSED_FOLDER, "tfidf_features.csv"))
    print(" Saved TF-IDF feature matrix to tfidf_features.csv")

    # after vectorizer.fit()
    idf = dict(zip(vectorizer.get_feature_names_out(), vectorizer.idf_))
    # Common terms (by doc frequency in TF-IDF)
    df_count = (X_tfidf>0).sum(axis=0)  # docs containing term
    common = sorted(zip(vectorizer.get_feature_names_out(), df_count.A1),
                key=lambda x: -x[1])[:50]
    print("Most ubiquitous terms:", common)

    # Combine into hybrid (scale & weight)
    tfidf_scaled = StandardScaler(with_mean=False).fit_transform(X_tfidf)
    struct_scaled = StandardScaler().fit_transform(df_structured.values)

    r_text = 0.86
    r_num  = 0.14
    n_text = tfidf_scaled.shape[1]
    n_num  = struct_scaled.shape[1]
    alpha  = np.sqrt(r_text / n_text) if n_text > 0 else 0.0
    beta   = np.sqrt(r_num  / n_num)  if n_num  > 0 else 0.0
    hybrid = hstack([alpha * tfidf_scaled, beta * struct_scaled])
    hybrid_arr = hybrid.toarray()

    # Wrap into DataFrame for inspection
    tfidf_terms  = vectorizer.get_feature_names_out().tolist()
    struct_terms = df_structured.columns.tolist()
    all_features = tfidf_terms + struct_terms
    hybrid_df = pd.DataFrame(hybrid_arr, index=documents.index, columns=all_features)
    print(f"\nHybrid feature matrix: {hybrid_df.shape[0]} logs × {hybrid_df.shape[1]} features")

    # Top-20 by variance
    variances = hybrid_df.var().sort_values(ascending=False)
    print("\nTop 20 features by variance (higher → more discriminative):")
    print(variances.head(20))

    # SVD loadings on the scaled & weighted hybrid
    svd = TruncatedSVD(n_components=2, random_state=42)
    svd.fit(hybrid)
    loadings = pd.DataFrame(
        svd.components_.T,
        index=all_features,
        columns=["SVD1","SVD2"]
    )
    for comp in loadings.columns:
        print(f"\nTop 15 terms in {comp}:")
        for term, weight in loadings[comp].abs().sort_values(ascending=False).head(15).items():
            print(f"  {term}: {weight:.4f}")

    out_csv = os.path.join(PARSED_FOLDER, "svd_full_loadings.csv")
    loadings.to_csv(out_csv, float_format="%.6f")
    print(f"\nSaved full SVD loadings to {out_csv}")

    # Save hybrid features
    np.save(HYBRID_FEATURES_FILE, hybrid_arr)
    print(f" Saved hybrid features to {HYBRID_FEATURES_FILE}")

    # Ground-truth mapping (noise: unknowns map to -1)  :contentReference[oaicite:1]{index=1}
    desired = {
        "otp_trimming.log":             0,
        "spi_errors_sim.log":           0,
        "upload_tdma.log":              1,
        "ic_startup.log":               1,
        "debounce_times.log":           2,
        "dsi3_crm_ecc_2_bit_error_sim.log": 5,
        "dsi3_crm.log":                 1,
        "dsi3_sync_pin_sim.log":        3,
        "register_access.log":          3,
        "dsi3_pdcm.log":                4,
        "dsi3_sync_pin.log":            4,
        "dsi3_clear_command_buffer.log":4,
        "interrupts_test_sim.log":      4,
        "shut_off.log":                 5,
        "dsi3_sync_channels.log":       5,
        "jtag_test.log":                6,
        "applicative_pattern.log":      7,
        "p52143_489.log":               7,
        "p52143_701.log":               8,
        "dsi3_pdcm_timing.log":         8,
        "dsi3_crc.log":                 8,
        "app_exm_in_spec.log":          8,
        "ic_status_word.log":           9,
        "dsi3_quiscent_current.log":   10,
        "dsi3_wait.log":               10,
        "dsi3_discovery_mode.log":     10,
        "otp_pulse_width.log":         10,
        "dsi3_crm_timing.log":         11,
        "spi_framing.log":             11,
        "sram_bist.log":               12,
    }
    y_true = np.array([ desired.get(f, -1) for f in documents.index ])  # :contentReference[oaicite:2]{index=2}

    # Dimensionality reduction for clustering (use SVD projection)
    X_reduced = svd.transform(hybrid)

    # ---------------- HDBSCAN ----------------
    clusterer = hdbscan.HDBSCAN(
        min_cluster_size=2,
        min_samples=1,
        metric='euclidean',
        cluster_selection_method='eom',
        cluster_selection_epsilon=0.00,
        allow_single_cluster=False,
        alpha=0.8,
    )
    hdb_labels = clusterer.fit_predict(X_reduced)

    # Metrics
    ari_hdb = adjusted_rand_score(y_true, hdb_labels)
    ami_hdb = adjusted_mutual_info_score(y_true, hdb_labels, average_method='arithmetic')

    print(f"\nHDBSCAN clustering metrics:")
    print(f"  Adjusted Rand Index (ARI):       {ari_hdb:.3f}")
    print(f"  Adjusted Mutual Information (AMI):{ami_hdb:.3f}")

    # Silhouette (excluding noise, only if ≥2 clusters)
    mask = hdb_labels != -1
    if len(set(hdb_labels[mask])) >= 2:
        sil = silhouette_score(X_reduced[mask], hdb_labels[mask])
        print(f"  Silhouette (noise removed): {sil:.3f}")
    else:
        print("  Skipping silhouette: need ≥2 clusters")

    # PPV for HDBSCAN (exclude noise bin -1)
    ppv_rows_hdb, macro_ppv_hdb = ppv_by_pred_bin(y_true, hdb_labels, exclude_pred_labels={-1})
    print("\nHDBSCAN PPV (per predicted bin; noise excluded):")
    for r in sorted(ppv_rows_hdb, key=lambda d: d["pred_bin"]):
        print(f"  bin={r['pred_bin']:>3}  hit_true={r['hit_true_label']:>3}  "
              f"hit={r['hit']:>2}  miss={r['miss']:>2}  total={r['total']:>2}  "
              f"PPV={r['ppv']*100:6.2f}%")
    micro_hdb = micro_ppv_from_rows(ppv_rows_hdb)
    print(f"Macro-PPV (HDBSCAN, no-noise): {macro_ppv_hdb*100:.2f}%")
    print(f"Micro-PPV (HDBSCAN, no-noise): {micro_hdb*100:.2f}%")

    # Files per HDBSCAN cluster
    clusters = defaultdict(list)
    for fname, lbl in zip(documents.index, hdb_labels):
        clusters[lbl].append(fname)

    print("\nHDBSCAN Files per Cluster (noise separate):")
    for lbl in sorted(clusters.keys()):
        name = "Noise Cluster" if lbl == -1 else f"Cluster {lbl}"
        files = clusters[lbl]
        print(f"\n{name} ({len(files)} files):")
        for f in files:
            print(f"  - {f}")

    # 2D plot HDBSCAN
    plt.figure(figsize=(10, 6))
    scatter = plt.scatter(
        X_reduced[:,0], X_reduced[:,1],
        c=hdb_labels,
        cmap='tab20',
        s=50,
        alpha=0.8,
        edgecolor='k'
    )
    plt.legend(
        *scatter.legend_elements(),
        title="HDBSCAN",
        bbox_to_anchor=(1.05,1),
        loc="upper left"
    )
    plt.title("HDBSCAN clusters on SVD-reduced features")
    plt.xlabel("SVD Component 1")
    plt.ylabel("SVD Component 2")
    plt.grid(True)
    for i, fname in enumerate(documents.index):
        x, y = X_reduced[i, 0], X_reduced[i, 1]
        plt.text(x, y, fname, fontsize=7, alpha=0.7, va='center', ha='center')
    plt.tight_layout()
    plt.show()

    # ---------------- K-Means (select best k by ARI) ----------------
    best_km = {"ari": -1, "k": None, "labels": None}
    for k in range(2, 11):
        labels_k = KMeans(n_clusters=k, random_state=42).fit_predict(X_reduced)
        ari_k    = adjusted_rand_score(y_true, labels_k)
        if ari_k > best_km["ari"]:
            best_km.update({"ari": ari_k, "k": k, "labels": labels_k})
    km_labels = best_km["labels"]

    # Compute metrics for the best-k labels (not the last loop)
    ami_km = adjusted_mutual_info_score(y_true, km_labels)
    sil_km = silhouette_score(X_reduced, km_labels)

    print("\nKMeans clustering metrics:")
    print(f"  Best k by ARI:                     {best_km['k']}")
    print(f"  Adjusted Rand Index (ARI):         {best_km['ari']:.3f}")
    print(f"  Adjusted Mutual Information (AMI): {ami_km:.3f}")
    print(f"  Silhouette:                        {sil_km:.3f}")

    # PPV for KMeans (no noise label)
    ppv_rows_km, macro_ppv_km = ppv_by_pred_bin(y_true, km_labels, exclude_pred_labels=None)
    print("\nKMeans PPV (per predicted bin):")
    for r in sorted(ppv_rows_km, key=lambda d: d["pred_bin"]):
        print(f"  bin={r['pred_bin']:>3}  hit_true={r['hit_true_label']:>3}  "
              f"hit={r['hit']:>2}  miss={r['miss']:>2}  total={r['total']:>2}  "
              f"PPV={r['ppv']*100:6.2f}%")
    micro_km = micro_ppv_from_rows(ppv_rows_km)
    print(f"Macro-PPV (KMeans): {macro_ppv_km*100:.2f}%")
    print(f"Micro-PPV (KMeans): {micro_km*100:.2f}%")

    # Files per KMeans cluster (best k)
    clusters_km = defaultdict(list)
    for fname, lbl in zip(documents.index, km_labels):
        clusters_km[lbl].append(fname)
    print("\nKMeans Files per Cluster:")
    for lbl in sorted(clusters_km):
        print(f"\nCluster {lbl} ({len(clusters_km[lbl])} files):")
        for f in clusters_km[lbl]:
            print(f"  - {f}")

    # 2D plot KMeans
    plt.figure(figsize=(10,6))
    scatter_km = plt.scatter(
        X_reduced[:,0], X_reduced[:,1],
        c=km_labels,
        cmap='Set2',
        s=50,
        alpha=0.8,
        edgecolor='k'
    )
    plt.legend(
        *scatter_km.legend_elements(),
        title="KMeans",
        bbox_to_anchor=(1.05,1),
        loc="upper left"
    )
    plt.title(f"KMeans (k={best_km['k']}) on SVD‐reduced features")
    plt.xlabel("SVD Component 1")
    plt.ylabel("SVD Component 2")
    plt.grid(True)
    for i, fname in enumerate(documents.index):
        x, y = X_reduced[i]
        plt.text(x, y, fname, fontsize=7, alpha=0.6, va="center", ha="center")
    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    main()
