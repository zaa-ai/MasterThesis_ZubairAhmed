from sklearn.cluster import DBSCAN
from sklearn.metrics import silhouette_score
from sklearn.preprocessing import StandardScaler
import numpy as np
import pandas as pd
import os
import matplotlib.pyplot as plt
from sklearn.decomposition import TruncatedSVD
from matplotlib.patches import Patch

# Shared Config
BASE_DIR = os.path.abspath(".")
LOG_FOLDER = os.path.join(BASE_DIR, "failing_logs_52144")
PARSED_FOLDER = os.path.join(LOG_FOLDER, "parsed")
STRUCTURED_LOG_FILE = os.path.join(PARSED_FOLDER, "uvm_log_structured.csv")
TFIDF_FEATURES_FILE = os.path.join(PARSED_FOLDER, "tfidf_features.npy")
STRUCTURED_FEATURES_FILE = os.path.join(PARSED_FOLDER, "structured_features.npy")
CLUSTER_LOG_FILE = os.path.join(PARSED_FOLDER, "logs_clusters.csv")

# Load data
tfidf_array = np.load(TFIDF_FEATURES_FILE)
structured_array = np.load(STRUCTURED_FEATURES_FILE)
df_logs = pd.read_csv(STRUCTURED_LOG_FILE)

# Filter logs to match structured input size
df_filtered = df_logs[df_logs["type"].isin(["UVM", "Simulator"])].copy().reset_index(drop=True)
df_filtered = df_filtered.groupby("file").first().reset_index()

# Match the number of rows to structured_array
if len(df_filtered) != len(structured_array):
    raise ValueError(f"Mismatch: {len(df_filtered)} log entries vs {len(structured_array)} structured vectors")

# Scale structured features
scaler = StandardScaler()
X_scaled = scaler.fit_transform(structured_array)

# Apply DBSCAN
tuned_eps = 2.0
min_samples = 1
dbscan = DBSCAN(eps=tuned_eps, min_samples=min_samples, metric="euclidean")
best_labels = dbscan.fit_predict(X_scaled)

# Silhouette Score
sil_score = -1
if len(set(best_labels)) > 1:
    sil_score = silhouette_score(X_scaled, best_labels)
print(f"\n🧠 Silhouette Score: {sil_score:.4f}")

# Assign labels to grouped filtered logs
df_filtered["cluster"] = best_labels

# Print file-to-cluster assignment
print("\n📁 File-to-Cluster Mapping:")
for file_name, cluster_id in zip(df_filtered["file"], best_labels):
    cluster_name = f"Cluster {cluster_id}" if cluster_id != -1 else "Noise"
    print(f"  {file_name} ➝ {cluster_name}")

# Merge clusters back to all logs by file name
df_logs = df_logs.copy()
df_logs["cluster"] = df_logs["file"].map(dict(zip(df_filtered["file"], best_labels)))

# Save clustered log file
df_logs.to_csv(CLUSTER_LOG_FILE, index=False)
print(f"\n✅ Clustered logs saved to: {CLUSTER_LOG_FILE}")

# Cluster summary
unique_labels, counts = np.unique(best_labels, return_counts=True)
print("\n📊 Cluster summary:")
for label, count in zip(unique_labels, counts):
    label_name = f"Cluster {label}" if label != -1 else "Noise"
    print(f"  {label_name}: {count} logs")

# 2D Visualization
svd = TruncatedSVD(n_components=2, random_state=42)
X_reduced = svd.fit_transform(X_scaled)

colors_palette = plt.cm.get_cmap("tab10", len(unique_labels))
colors = [colors_palette(i) for i in range(len(unique_labels))]
label_to_color = {label: colors[i] for i, label in enumerate(unique_labels)}
color_assignment = [label_to_color[label] for label in best_labels]

plt.figure(figsize=(10, 6))
plt.scatter(X_reduced[:, 0], X_reduced[:, 1], c=color_assignment, s=40, edgecolor="black", alpha=0.8)
plt.title("DBSCAN Clustering (Structured Features - Scaled)")
plt.xlabel("SVD Component 1")
plt.ylabel("SVD Component 2")
plt.grid(True)

legend_labels = [
    Patch(color=label_to_color[label], label=f"Cluster {label}" if label != -1 else "Noise")
    for label in unique_labels
]
plt.legend(handles=legend_labels, title="Clusters", bbox_to_anchor=(1.05, 1), loc='upper left')
plt.tight_layout()
plt.show()

