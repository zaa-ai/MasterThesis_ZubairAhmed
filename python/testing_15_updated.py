import os
import re
import pandas as pd
import numpy as np
import string
import hdbscan
import csv
from collections import defaultdict
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.decomposition import TruncatedSVD
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import adjusted_rand_score, adjusted_mutual_info_score, silhouette_score
import matplotlib.pyplot as plt
from scipy.sparse import hstack
from sklearn.cluster import KMeans
from collections import defaultdict
from sklearn.neighbors import NearestNeighbors
from matplotlib.lines import Line2D
from matplotlib.colors import ListedColormap


# Paths
BASE_DIR = os.path.abspath(".")
LOG_FOLDER = os.path.join(BASE_DIR, "failing_logs_52144")
PARSED_FOLDER = os.path.join(LOG_FOLDER, "parsed")
os.makedirs(PARSED_FOLDER, exist_ok=True)

STRUCTURED_LOG_FILE = os.path.join(PARSED_FOLDER, "uvm_log_structured.csv")
TFIDF_FEATURES_FILE = os.path.join(PARSED_FOLDER, "tfidf_features.npy")
STRUCTURED_FEATURES_FILE = os.path.join(PARSED_FOLDER, "structured_features.npy")
HYBRID_FEATURES_FILE = os.path.join(PARSED_FOLDER, "hybrid_features.npy")
CLUSTER_LOG_FILE       = os.path.join(PARSED_FOLDER, 'logs_clusters.csv')

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
#Segregate passsing and Failing logs
def is_failing_log(content: str) -> bool:
    # Quick simulator pattern match
    if SIM_WARNING_PATTERN.search(content):
        return True
    # Structured UVM pattern match
    for line in content.splitlines():
        m = UVM_LOG_PATTERN.match(line.strip())
        if m:
            if m.group("severity") in ("UVM_ERROR", "UVM_FATAL"):
                return True
    return False

#Classify logs
def classify_logs(logs):
    passing, failing = [], []
    for fname, content in logs:
        if is_failing_log(content):
            failing.append((fname, content))
        else:
            passing.append((fname, content))
    return passing, failing
#save logs
def save_classification(passing, failing, out_csv):
    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["file", "status"])
        for fname, _ in sorted(passing):
            w.writerow([fname, "PASS"])
        for fname, _ in sorted(failing):
            w.writerow([fname, "FAIL"])

# Preprocessing to split alphanumeric blocks

def split_alphanum(text: str) -> str:
    """
    Insert spaces between letter→digit and digit→letter boundaries
    to prevent concatenated tokens.
    """
    text = re.sub(r'(?<=[A-Za-z])(?=[0-9])', ' ', text)
    text = re.sub(r'(?<=[0-9])(?=[A-Za-z])', ' ', text)
    return text
# Clean text
def clean_text(text):
    # lower-case and split alphanumeric sequences
    text = split_alphanum(str(text).lower())
    return text.translate(str.maketrans("", "", string.punctuation))

# Load logs
def load_logs(log_directory):
    logs = []
    for filename in os.listdir(log_directory):
        if filename.endswith(".log"):
            filepath = os.path.join(log_directory, filename)
            with open(filepath, 'r', encoding='utf-8', errors='ignore') as file:
                content = file.read()
                logs.append((filename, content))
    return logs

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
                    "time_us": 0,
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
                    "time_us": 0,
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
        row["first_error_time"] = group[group.severity == "UVM_ERROR"]["time_us"].min() if "UVM_ERROR" in group.severity.values else 0
        row["last_error_time"] = group[group.severity == "UVM_ERROR"]["time_us"].max() if "UVM_ERROR" in group.severity.values else 0

        feature_list.append(row)
    df_structured = pd.DataFrame(feature_list).fillna(0)
    df_structured.set_index("file", inplace=True)
    np.save(STRUCTURED_FEATURES_FILE, df_structured.values)
    return df_structured

# Text document creation per log file
def create_document_per_log(df, context_lines=0):
    """
    For each file, extract only the first UVM_ERROR message, plus optional context.
    Returns a pandas Series: file ➝ clean message text.
    """
    documents = {}
    grouped = df[df["type"] == "UVM"].groupby("file")
    for filename, group in grouped:
        group = group.reset_index(drop=True)
        first_error_idx = group[group["severity"] == "UVM_ERROR"].index.min()
        if pd.isna(first_error_idx):
            # fallback: no UVM_ERROR in this log
            message = group["message"].iloc[0] if not group.empty else ""
            documents[filename] = clean_text(message)
            continue
        # Ensure we don't go out of bounds
        end_idx = int(first_error_idx + context_lines + 1)
        selected_msgs = group.loc[first_error_idx:end_idx, "message"]
        doc = " ".join(clean_text(msg) for msg in selected_msgs)
        documents[filename] = doc
        # #print in terminal to see the first UVM_ERROR is being considered
        # print(f" {filename} → First UVM_ERROR: {selected_msgs.iloc[0]}")
        # # Debug output
        # print(f" {filename} — First error at index {first_error_idx}, grabbing {context_lines + 1} lines")
        # print(" Captured lines:")
        # print(group.loc[first_error_idx:end_idx, "message"].to_string(index=False))
        # print("-" * 80)

    return pd.Series(documents)

def plot_clusters_2d_fixed(
    X2d,
    labels,
    title="Clusters on 2D projection",
    legend_title="Clusters",
    noise_label=-1,
    force_noise_red=True,
    palette=None
):
    """
    Robust 2D scatter for clustering with correct color/legend mapping.
    - If noise_label is present, it's mapped to color index 0 (red by default).
    - Other labels get bright colors, consistent between points and legend.
    - No filename annotations (keeps plot readable).
    """

    y = np.asarray(labels)

    # Unique labels in a stable order: noise first (if present), then the rest sorted
    uniq = np.unique(y)
    ordered = []
    if noise_label is not None and noise_label in uniq:
        ordered.append(noise_label)
    ordered += [u for u in uniq if (noise_label is None or u != noise_label)]

    # Bright palette (first color reserved for noise red)
    default_palette = [
        "#e41a1c",  # red (noise)
        "#377eb8",  # blue
        "#4daf4a",  # green
        "#984ea3",  # purple
        "#ff7f00",  # orange
        "#ffff33",  # yellow
        "#a65628",  # brown
        "#f781bf",  # pink
        "#66c2a5",  # teal
        "#fc8d62",  # salmon
        "#8da0cb",  # light purple
        "#e78ac3",  # magenta
        "#a6d854",  # lime
        "#ffd92f",  # bright yellow
        "#b3b3b3",  # gray
    ]
    colors = list(palette) if palette is not None else default_palette[:]

    # If we don't want forced red for noise, rotate palette normally
    if not force_noise_red and noise_label in ordered:
        # move red away so clusters cycle normally
        colors[0] = "#377eb8"

    # Build label -> color index mapping
    label_to_cid = {}
    next_cid = 0
    for lab in ordered:
        if lab == noise_label and force_noise_red:
            label_to_cid[lab] = 0
        else:
            if lab == noise_label and not force_noise_red and next_cid == 0:
                # if not forcing red and noise sits first, just assign next color
                label_to_cid[lab] = 0
                next_cid = 1
                continue
            label_to_cid[lab] = next_cid
        next_cid += 1

    needed = max(label_to_cid.values()) + 1
    # Extend/repeat colors if more clusters than palette
    if needed > len(colors):
        times = (needed // len(colors)) + 1
        colors = (colors * times)[:needed]
    else:
        colors = colors[:needed]

    cmap = ListedColormap(colors)

    # Convert labels to color-ids
    color_ids = np.array([label_to_cid[lab] for lab in y], dtype=int)

    # Scatter with fixed normalization so legend/colors are consistent
    plt.figure(figsize=(10, 6))
    plt.scatter(
        X2d[:, 0], X2d[:, 1],
        c=color_ids,
        s=60,
        alpha=0.9,
        edgecolor="k",
        cmap=cmap,
        vmin=0,
        vmax=needed - 1
    )

    # Build ONE legend: color chip + cluster name + count
    handles, labels_txt = [], []
    _, counts = np.unique(y, return_counts=True)
    # Need counts per ordered label (match mapping)
    label_to_count = {lab: int(np.sum(y == lab)) for lab in ordered}
    for lab in ordered:
        cid = label_to_cid[lab]
        color = colors[cid]
        marker = Line2D([0],[0], marker='o', color='w',
                        markerfacecolor=color, markeredgecolor='k',
                        markersize=8)
        handles.append(marker)
        name = "Noise" if (noise_label is not None and lab == noise_label) else f"Cluster {int(lab)}"
        labels_txt.append(f"{name} ({label_to_count[lab]})")

    plt.legend(
        handles, labels_txt,
        title=legend_title,
        bbox_to_anchor=(1.02, 1),
        loc="upper left",
        borderaxespad=0.0
    )

    plt.title(title)
    plt.xlabel("SVD Component 1")
    plt.ylabel("SVD Component 2")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.show()

# Main
def main():
    logs = load_logs(LOG_FOLDER)
    
    # Step 1: Classify logs
    passing_logs, failing_logs = classify_logs(logs)

    print("\nPASSING logs (skipped from clustering):")
    for fname, _ in sorted(passing_logs):
        print(f"  - {fname}")

    print("\nFAILING logs (processed further):")
    for fname, _ in sorted(failing_logs):
        print(f"  - {fname}")

    # Optional: save manifest
    save_classification(
        passing_logs,
        failing_logs,
        os.path.join(PARSED_FOLDER, "log_classification.csv")
    )
    print(f"\nSaved classification to {os.path.join(PARSED_FOLDER, 'log_classification.csv')}")

    if not failing_logs:
        print("\nNo failing logs found. Exiting without clustering.")
        return
    
    df = extract_log_info(logs)
    df.to_csv(STRUCTURED_LOG_FILE, index=False)
    print(f"Saved structured log entries to {STRUCTURED_LOG_FILE}")

    # Structured numeric features
    df_structured = extract_structured_features(df)
    print(f"Saved structured numeric features to {STRUCTURED_FEATURES_FILE}")
    
    # Domain-specific stopwords
    extended_stop = [
    "packet","header","channel","count","period","difference",
    "recorded","injected","failed","unable","comerr",
    "data","value","word","status","x"] #extra stop words in more log files
    # TF-IDF Features
    documents = create_document_per_log(df, context_lines=0)
    df_structured = df_structured.reindex(documents.index).fillna(0)
    #print("\n TF-IDF Input Preview:")
    # for fname, doc in documents.items():
    #     print(f"\n--- {fname} ---\n{doc[:500]}...\n")  # show first 500 chars
    #n_docs = len(documents)

    vectorizer = TfidfVectorizer(
        preprocessor=clean_text,
        stop_words=extended_stop,           # now a bigger blacklist
        token_pattern=r"(?u)\b[a-z][a-z]{2,}\b",  # only 3+ letter words
        ngram_range=(1,1),                  # allow up to trigrams
        min_df=max(1, int(0.09 * len(documents))),
        #min_df=int(0.09*len(documents)),     # token must appear in ≥10% of logs
        max_df=0.60,                         # drop tokens in >60% of logs
        max_features=1500,                  # slightly larger vocab
        sublinear_tf=True,
        norm="l2"
    )
    X_tfidf = vectorizer.fit_transform(documents.values)
    # print out every parameter that was used by the vectorizer
    print("\nTF-IDF Vectorizer parameters actually used:")
    for param, val in vectorizer.get_params().items():
        print(f"  {param}: {val}")

    np.save(TFIDF_FEATURES_FILE, X_tfidf.toarray())
    print(f" Saved TF-IDF features to {TFIDF_FEATURES_FILE}")
    tfidf_df = pd.DataFrame(X_tfidf.toarray(), index=documents.index, columns=vectorizer.get_feature_names_out())
    tfidf_df.to_csv(os.path.join(PARSED_FOLDER, "tfidf_features.csv"))
    print(" Saved TF-IDF feature matrix to tfidf_features.csv")
    # after vectorizer.fit()
    idf = dict(zip(vectorizer.get_feature_names_out(), vectorizer.idf_))
    # Sort by lowest variance / highest df
    df_count = (X_tfidf>0).sum(axis=0)  # docs containing term
    common = sorted(zip(vectorizer.get_feature_names_out(), df_count.A1),
                key=lambda x: -x[1])[:50]
    print("Most ubiquitous terms:", common)
        # Combine into hybrid
    # Scale TF-IDF (sparse) and structured (dense) to unit‐variance
    tfidf_scaled = StandardScaler(with_mean=False).fit_transform(X_tfidf)
    struct_scaled = StandardScaler().fit_transform(df_structured.values)

    # 6) Weight blocks with custom ratio
    r_text = 0.86  # 40% text
    r_num  = 0.14  # 60% numeric
    n_text = tfidf_scaled.shape[1]
    n_num  = struct_scaled.shape[1]
    alpha  = np.sqrt(r_text / n_text)
    beta   = np.sqrt(r_num  / n_num)
    hybrid = hstack([alpha * tfidf_scaled, beta * struct_scaled])
    hybrid_arr = hybrid.toarray()

    # 1) Build column names
    tfidf_terms  = vectorizer.get_feature_names_out().tolist()
    struct_terms = df_structured.columns.tolist()
    all_features = tfidf_terms + struct_terms

    # 2) Wrap into DataFrame for inspection
    hybrid_df = pd.DataFrame(
        hybrid_arr,
        index=documents.index,
        columns=all_features
    )
    print(f"\nHybrid feature matrix: {hybrid_df.shape[0]} logs × {hybrid_df.shape[1]} features")

    # 3) Top-20 by variance
    variances = hybrid_df.var().sort_values(ascending=False)
    print("\nTop 20 features by variance (higher → more discriminative):")
    print(variances.head(20))

    # 4) SVD loadings on the *scaled & weighted* hybrid
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

    # Save and visualize using the same hybrid
    np.save(HYBRID_FEATURES_FILE, hybrid_arr)
    print(f" Saved hybrid features to {HYBRID_FEATURES_FILE}")

    desired = {
    "otp_trimming.log":             0,
    "spi_errors_sim.log":           0,
    "upload_tdma.log":              1,
    "ic_startup.log":               1,
    "debounce_times.log":           2,
    "dsi3_crm_ecc_2_bit_error_sim.log": 3,
    "dsi3_crm.log":                 1,
    "dsi3_sync_pin_sim.log":        4,
    "register_access.log":          5,
    "dsi3_pdcm.log":                6,
    "dsi3_sync_pin.log":            6,
    "dsi3_clear_command_buffer.log":4,
    "interrupts_test_sim.log":      6,
    "shut_off.log":                 3,
    "dsi3_sync_channels.log":       3,
    "jtag_test.log":                7,
    "applicative_pattern.log":      8,
    "p52143_489.log":               8,
    "p52143_701.log":               9,
    "dsi3_pdcm_timing.log":         9,
    "dsi3_crc.log":                 9,
    "app_exm_in_spec.log":          9,
    "ic_status_word.log":           10,
    "dsi3_quiscent_current.log":   11,
    "dsi3_wait.log":               11,
    "dsi3_discovery_mode.log":     11,
    "otp_pulse_width.log":         11,
    "dsi3_crm_timing.log":         12,
    "spi_framing.log":             12,
    "sram_bist.log":               13, 
     }
        # 1) Build your ground‐truth label array in the same order as 'documents.index'
    y_true = np.array([ desired.get(f, -1) for f in documents.index ])

    X_reduced = svd.transform(hybrid)
    
    # 1) Configure & fit
#   - min_cluster_size: smallest group you care about (e.g. 2, 3, 4…)
#   - min_samples: how conservative you want noise detection (None→auto)
    clusterer = hdbscan.HDBSCAN(
        min_cluster_size=2,
        min_samples=1,
        metric='euclidean',
        cluster_selection_method='eom',   # “excess of mass- eom” cluster extraction
        cluster_selection_epsilon=0.00,    # shave off 0.05 in stability threshold to absorb border points
        allow_single_cluster= False,
        alpha=0.8,                      # lower alpha (closer to 1.0) → less aggressive hierarchy condensation
    )
    hdb_labels = clusterer.fit_predict(X_reduced)   # or hybrid_arr for full-dim clustering
    # Compute clustering‐quality metrics against your ground truth y_true
    ari_hdb = adjusted_rand_score(y_true, hdb_labels)
    ami_hdb = adjusted_mutual_info_score(y_true, hdb_labels, average_method='arithmetic')

    print(f"\nHDBSCAN clustering metrics:")
    print(f"  Adjusted Rand Index (ARI):       {ari_hdb:.3f}")
    print(f"  Adjusted Mutual Information (AMI):{ami_hdb:.3f}")

    # 2) Print cluster counts & noise fraction
    unique, counts = np.unique(hdb_labels, return_counts=True)
    print("\nHDBSCAN clustering summary:")
    total = len(hdb_labels)
    for lbl, cnt in zip(unique, counts):
        name = "Noise" if lbl == -1 else f"Cluster {lbl}"
        print(f"  {name:>8}: {cnt} points ({cnt/total*100:.1f}%)")

    # 3) Silhouette (excluding noise, only if ≥2 clusters)
    mask = hdb_labels != -1
    if len(set(hdb_labels[mask])) >= 2:
        sil = silhouette_score(X_reduced[mask], hdb_labels[mask])
        print(f"  Silhouette (noise removed): {sil:.3f}")
    else:
        print("  Skipping silhouette: need ≥2 clusters")
    # 4) Post-process noise points: snap each noise point to its own cluster, thus better clustering
    # 4) Build a dict: label → list of filenames (noise stays as -1)
    clusters = defaultdict(list)
    for fname, lbl in zip(documents.index, hdb_labels):
        clusters[lbl].append(fname)

    # 5) Print summary, treating -1 as “Noise Cluster”
    print("\nHDBSCAN Files per Cluster (noise separate):")
    for lbl in sorted(clusters.keys()):
        name = "Noise Cluster" if lbl == -1 else f"Cluster {lbl}"
        files = clusters[lbl]
        print(f"\n{name} ({len(files)} files):")
        for f in files:
            print(f"  - {f}")
    
    plot_clusters_2d_fixed(
    X_reduced,
    hdb_labels,
    title="HDBSCAN clusters on SVD-reduced features",
    legend_title="HDBSCAN",
    noise_label=-1,          # HDBSCAN noise
    force_noise_red=True     # keep noise always red
)

    # 2) Inspect the distribution of your manual labels
    # unique, counts = np.unique(y_true, return_counts=True)
    # print("\nManual cluster label distribution:")
    # for lbl, cnt in zip(unique, counts):
    #     name = "MISSING" if lbl == -1 else f"Cluster {lbl}"
    #     print(f"  {name:>8}: {cnt} files")

    # # 3) Sanity check: ensure no “-1” labels
    # if -1 in unique:
    #     missing = np.sum(y_true == -1)
    #     raise ValueError(f"You have {missing} files not in your desired mapping! "
    #                     "Please correct your desired dict to include them.")
    # # 4) List the missing filenames
    # missing_files = [f for f in documents.index if desired.get(f, -1) == -1]
    # print("\nFiles not in your desired mapping (missing):")
    # for f in missing_files:
    #     print("  -", f)
    
    # desired_n = len(set(desired.values())) # desired_n == 13 (the actual number of unique clusters you defined)
    # best = {"ari": -1, "eps": None, "min_samples": None}
    #min_clusters, max_clusters = 10, 14
    #best = {"ari": -1, "eps": None, "min_samples": None, "n_clusters": 0}

     # K-Means hyperparameter tuning (via Adjusted Rand Index) 

    # 1) Prepare a separate “best” holder for KMeans
    best_km = {"ari": -1, "k": None}

    # 2) Loop over candidate k values
    for k in range(2, 11):
        km_labels = KMeans(n_clusters=k, random_state=42).fit_predict(X_reduced)
        ari_k    = adjusted_rand_score(y_true, km_labels)
        ami_km = adjusted_mutual_info_score(y_true, km_labels)
        sil_km = silhouette_score(X_reduced, km_labels)
        if ari_k > best_km["ari"]:
            best_km.update({"ari": ari_k, "k": k})
    print(f"Best KMeans → k={best_km['k']} (ARI={best_km['ari']:.3f})")
    print(f"KMeans AMI: {ami_km:.3f}, silhouette: {sil_km:.3f}")

    # 3) Print cluster counts
    unique, counts = np.unique(km_labels, return_counts=True)
    print("\nKMeans clustering summary:")
    total = len(km_labels)
    for lbl, cnt in zip(unique, counts):
        name = f"Cluster {lbl}"
        pct  = cnt/total*100
        print(f"  {name:>8}: {cnt} points ({pct:.1f}%)")

# 4) Files per cluster
    
    clusters_km = defaultdict(list)
    for fname, lbl in zip(documents.index, km_labels):
        clusters_km[lbl].append(fname)

    print("\nKMeans Files per Cluster:")
    for lbl in sorted(clusters_km):
        print(f"\nCluster {lbl} ({len(clusters_km[lbl])} files):")
        for f in clusters_km[lbl]:
            print(f"  - {f}")

    plot_clusters_2d_fixed(
    X_reduced,
    km_labels,
    title=f"KMeans (k={best_km['k']}) on SVD-reduced features",
    legend_title="KMeans",
    noise_label=None,        # KMeans doesn't use -1
    force_noise_red=False
)


if __name__ == "__main__":
    main()
