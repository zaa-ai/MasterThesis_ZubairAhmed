import os
import re
import pandas as pd
import numpy as np
import string
from collections import defaultdict
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.decomposition import TruncatedSVD
from sklearn.preprocessing import StandardScaler
import matplotlib.pyplot as plt

# Paths
BASE_DIR = os.path.abspath(".")
LOG_FOLDER = os.path.join(BASE_DIR, "failing_logs_52144")
PARSED_FOLDER = os.path.join(LOG_FOLDER, "parsed")
os.makedirs(PARSED_FOLDER, exist_ok=True)

STRUCTURED_LOG_FILE = os.path.join(PARSED_FOLDER, "uvm_log_structured.csv")
TFIDF_FEATURES_FILE = os.path.join(PARSED_FOLDER, "tfidf_features.npy")
STRUCTURED_FEATURES_FILE = os.path.join(PARSED_FOLDER, "structured_features.npy")
HYBRID_FEATURES_FILE = os.path.join(PARSED_FOLDER, "hybrid_features.npy")

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

# Clean text
def clean_text(text):
    text = str(text).lower()
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
def create_document_per_log(df):
    log_docs = df[df["type"].isin(["UVM", "Simulator"])].copy()
    log_docs["clean_msg"] = log_docs["message"].apply(clean_text)
    grouped = log_docs.groupby("file")["clean_msg"].apply(lambda msgs: " ".join(msgs))
    return grouped

# Main
def main():
    logs = load_logs(LOG_FOLDER)
    df = extract_log_info(logs)
    df.to_csv(STRUCTURED_LOG_FILE, index=False)
    print(f"✅ Saved structured log entries to {STRUCTURED_LOG_FILE}")

    # Structured numeric features
    df_structured = extract_structured_features(df)
    print(f"✅ Saved structured numeric features to {STRUCTURED_FEATURES_FILE}")

    # Domain-specific stopwords
    custom_stopwords = [
    "uvm", "info", "error", "warning", "fatal", "test", "run", "reporter", "cmd", "sim",
    "time", "status", "us", "phase", "sequence", "object", "line", "file", "log", "default",
    "component", "module", "top", "start", "end", "begin", "ready", "process", "value", "config",
    "setting", "parameter", "override", "verbosity", "monitor", "driver", "agent", "interface"
    ]
    # TF-IDF Features
    documents = create_document_per_log(df)
    vectorizer = TfidfVectorizer(
        stop_words=custom_stopwords,
        ngram_range=(1, 2),
        max_features=1000,
        min_df=1,
        sublinear_tf=True,
        norm="l2"
    )
    X_tfidf = vectorizer.fit_transform(documents.values)
    np.save(TFIDF_FEATURES_FILE, X_tfidf.toarray())
    print(f"✅ Saved TF-IDF features to {TFIDF_FEATURES_FILE}")

    # Combine into hybrid
    scaler = StandardScaler()
    X_structured_scaled = scaler.fit_transform(df_structured.values)
    hybrid_features = np.hstack([X_tfidf.toarray(), X_structured_scaled])
    np.save(HYBRID_FEATURES_FILE, hybrid_features)
    print(f"✅ Saved hybrid features to {HYBRID_FEATURES_FILE}")

    # Visualize
    svd = TruncatedSVD(n_components=2, random_state=42)
    X_reduced = svd.fit_transform(hybrid_features)
    plt.figure(figsize=(10, 6))
    plt.scatter(X_reduced[:, 0], X_reduced[:, 1], s=40, alpha=0.7)
    for i, name in enumerate(documents.index):
        plt.text(X_reduced[i, 0], X_reduced[i, 1], name, fontsize=8, alpha=0.6)
    plt.title("2D Projection of Hybrid Log Features")
    plt.xlabel("SVD Component 1")
    plt.ylabel("SVD Component 2")
    plt.grid(True)
    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    main()
