import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from collections import defaultdict
from sklearn.preprocessing import StandardScaler
from sklearn.cluster import DBSCAN, KMeans
from sklearn.neighbors import NearestNeighbors
from sklearn.metrics import silhouette_score
from sklearn.decomposition import TruncatedSVD

# --- Paths & Config ---------------------------------------------------------
BASE_DIR = os.path.abspath('.')
PARSED_FOLDER = os.path.join(BASE_DIR, 'failing_logs_52144', 'parsed')
STRUCTURED_LOG_FILE    = os.path.join(PARSED_FOLDER, 'uvm_log_structured.csv')
HYBRID_FEATURES_FILE   = os.path.join(PARSED_FOLDER, 'hybrid_features.npy')
CLUSTER_LOG_FILE       = os.path.join(PARSED_FOLDER, 'logs_clusters.csv')
TFIDF_FEATURES_FILE    = os.path.join(PARSED_FOLDER, 'tfidf_features.npy')
STRUCTURED_FEATURES_FILE = os.path.join(PARSED_FOLDER, 'structured_features.npy')
# --- Load Data --------------------------------------------------------------
#hybrid_array = np.load(STRUCTURED_FEATURES_FILE)
hybrid_array = np.load(HYBRID_FEATURES_FILE)
#hybrid_array = np.load(TFIDF_FEATURES_FILE)
df_logs = pd.read_csv(STRUCTURED_LOG_FILE)

# Align one row per file
df_filtered = (
    df_logs[df_logs['type'].isin(['UVM','Simulator'])]
    .groupby('file').first()
    .reset_index()
)
assert len(df_filtered) == hybrid_array.shape[0], \
    f"Mismatch: {len(df_filtered)} files vs {hybrid_array.shape[0]} feature rows"

# --- Preprocessing ----------------------------------------------------------
# Standardize
scaler = StandardScaler()
X = scaler.fit_transform(hybrid_array)

# --- Grid Search DBSCAN -----------------------------------------------------
def grid_search_dbscan(X, eps_vals, min_samples_list, metric='cosine'):
    best = {'score': -1, 'eps': None, 'min_samples': None, 'labels': None}
    for eps in eps_vals:
        for ms in min_samples_list:
            db = DBSCAN(eps=eps, min_samples=ms, metric=metric).fit(X)
            labels = db.labels_
            n_clusters = len(set(labels) - {-1})
            noise_frac = np.mean(labels == -1)
            if n_clusters < 2 or noise_frac > 0.2:
                continue
            score = silhouette_score(X, labels, metric=metric)
            if score > best['score']:
                best.update({'score': score, 'eps': eps, 'min_samples': ms, 'labels': labels})
    return best

# Define search space
eps_vals = np.linspace(0.1, 1.0, 20)
min_samples_list = [2,3,4,5]
# Perform search
best_db = grid_search_dbscan(X, eps_vals, min_samples_list, metric='cosine')
if best_db['eps'] is not None:
    print(f"Best DBSCAN -> eps={best_db['eps']:.3f}, min_samples={best_db['min_samples']}, silhouette={best_db['score']:.3f}")
    labels_db = best_db['labels']
else:
    print("No DBSCAN configuration produced ≥2 clusters with ≤20% noise.")
    labels_db = None

# --- KMeans Fallback -------------------------------------------------------
kmeans_scores = []
for k in range(2, 8):
    km = KMeans(n_clusters=k, random_state=42).fit(X)
    sc = silhouette_score(X, km.labels_, metric='cosine')
    kmeans_scores.append((k, sc))
print("KMeans silhouette by k:", kmeans_scores)
best_k, best_sc = max(kmeans_scores, key=lambda x: x[1])
print(f"Best KMeans -> k={best_k}, silhouette={best_sc:.3f}")
labels_km = KMeans(n_clusters=best_k, random_state=42).fit_predict(X)

# --- Choose final labels (DBSCAN preferred, else KMeans) ---------------------
if labels_db is not None:
    final_labels = labels_db.copy()
    method = 'DBSCAN'
else:
    final_labels = labels_km.copy()
    method = 'KMeans'
print(f"Using {method} for initial clusters (noise will be reassigned)")

# --- Reassign noise points to clusters or treat as standalone ---------------
unique_labels = [l for l in sorted(set(final_labels)) if l != -1]
if unique_labels:
    # Compute centroids in feature space
    centroids = np.vstack([X[final_labels == c].mean(axis=0) for c in unique_labels])
    for i, lab in enumerate(final_labels):
        if lab == -1:
            # assign to nearest centroid
            dists = np.linalg.norm(centroids - X[i], axis=1)
            final_labels[i] = unique_labels[int(dists.argmin())]
else:
    # no clusters found: assign each point its own cluster id
    final_labels = np.arange(len(final_labels))
    method = 'All-Singleton'
    print("No clusters found; treating each log as its own cluster.")

# --- Save & Summarize ------------------------------------------------------
df_filtered['cluster'] = final_labels
df_logs['cluster'] = df_logs['file'].map(dict(zip(df_filtered['file'], final_labels)))
pd.Series(final_labels).value_counts().sort_index()
df_logs.to_csv(CLUSTER_LOG_FILE, index=False)
cluster_counts = pd.Series(final_labels).value_counts().sort_index()
print("Cluster counts (label: count):")
print(cluster_counts.to_string()) 

# --- Visualization ---------------------------------------------------------
# 2D projection
coords = TruncatedSVD(n_components=2, random_state=42).fit_transform(X)

# Prepare color palette for clusters
cluster_ids = sorted(set(final_labels))
palette = plt.cm.get_cmap('tab10', len(cluster_ids))
label_colors = {lbl: palette(i) for i, lbl in enumerate(cluster_ids)}

# Identify originally noisy points (before reassignment)
if labels_db is not None:
    original_noise = {i for i, l in enumerate(labels_db) if l == -1}
else:
    original_noise = set()

plt.figure(figsize=(10, 8))
for lbl in cluster_ids:
    idxs = [i for i, l in enumerate(final_labels) if l == lbl]
    # Separate noise-reassigned vs. regular points
    reassigned = [i for i in idxs if i in original_noise]
    regular = [i for i in idxs if i not in original_noise]

    # Plot regular cluster points
    color = label_colors.get(lbl, (0.5,0.5,0.5))
    plt.scatter(
        coords[regular, 0], coords[regular, 1],
        c=[color], s=80, label=f"Cluster {lbl}"
    )
    # Plot reassigned noise in red
    if reassigned:
        plt.scatter(
            coords[reassigned, 0], coords[reassigned, 1],
            c='red', marker='x', s=100,
            label=f"Reassigned Noise {lbl}"
        )
    # annotate all points
    for i in idxs:
        plt.text(
            coords[i, 0], coords[i, 1], df_filtered.loc[i, 'file'],
            fontsize=8, alpha=0.7
        )

plt.title(f'{method} Clustering with File Labels')
plt.xlabel('Component 1')
plt.ylabel('Component 2')
plt.legend(title='Clusters & Reassigned Noise', bbox_to_anchor=(1.05, 1), loc='upper left')
plt.grid(True)
plt.tight_layout()
plt.show()