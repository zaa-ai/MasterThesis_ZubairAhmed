import os
import re
import pandas as pd
import numpy as np
import string
from collections import defaultdict
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.decomposition import TruncatedSVD
import matplotlib.pyplot as plt

# Define Paths
BASE_DIR = os.path.abspath(".")
LOG_FOLDER = os.path.join(BASE_DIR, "single")
PARSED_FOLDER = os.path.join(LOG_FOLDER, "parsed")
STRUCTURED_LOG_FILE = os.path.join(PARSED_FOLDER, "uvm_log_structured.csv")
STRUCTURED_FEATURES_FILE = os.path.join(PARSED_FOLDER, "structured_features.npy")
TFIDF_FEATURES_FILE = os.path.join(PARSED_FOLDER, "tfidf_features.npy")

# Ensure parsed folder exists
os.makedirs(PARSED_FOLDER, exist_ok=True)

# Regex Patterns
UVM_LOG_PATTERN = re.compile(
    r"(?P<severity>UVM_INFO|UVM_WARNING|UVM_ERROR|UVM_FATAL)\s+"
    r"@\s+(?P<time>[0-9\.]+)us:\s+"
    r"\[(?P<module>[^\]]+)\]\s+"
    r"(?P<message>.+?)(?:\s+\S+\(\d+\))?$"
)

CONFIG_PATTERN = re.compile(
    r"\+(?P<key>UVM_TESTNAME|uvm_set_type_override|UVM_VERBOSITY)=(?P<value>[\w\.\-]+)"
)

SIM_WARNING_PATTERN = re.compile(
    r"(Null object access|constraint solver failure|Segmentation fault|coverage illegal hit)",
    re.IGNORECASE
)

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

# Extract log info
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
    return extracted

# Feature engineering per file
def aggregate_features(df):
    feature_list = []
    grouped = df.groupby("file")
    for filename, group in grouped:
        row = defaultdict(int)
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

    df_feat = pd.DataFrame(feature_list)
    df_feat.fillna(0, inplace=True)
    df_feat.to_csv(os.path.join(PARSED_FOLDER, "aggregated_features.csv"), index=False)
    np.save(STRUCTURED_FEATURES_FILE, df_feat.drop("file", axis=1).values)
    return df_feat

# Visualize features with Truncated SVD
def visualize_features(df_feat):
    X = df_feat.drop("file", axis=1).values
    svd = TruncatedSVD(n_components=2, random_state=42)
    X_reduced = svd.fit_transform(X)

    plt.figure(figsize=(10, 6))
    plt.scatter(X_reduced[:, 0], X_reduced[:, 1], s=40, alpha=0.7)
    for i, name in enumerate(df_feat["file"]):
        plt.text(X_reduced[i, 0], X_reduced[i, 1], name, fontsize=8, alpha=0.6)
    plt.title("2D Projection of Structured Log Features")
    plt.xlabel("Component 1")
    plt.ylabel("Component 2")
    plt.grid(True)
    plt.tight_layout()
    plt.show()

# Main pipeline
def main():
    logs = load_logs(LOG_FOLDER)
    extracted = extract_log_info(logs)
    df = pd.DataFrame(extracted)
    df.to_csv(STRUCTURED_LOG_FILE, index=False)
    print(f"Saved structured logs to {STRUCTURED_LOG_FILE}")
    df_feat = aggregate_features(df)
    print(f"Saved structured feature vectors to {STRUCTURED_FEATURES_FILE}")
    visualize_features(df_feat)

if __name__ == "__main__":
    main()
