#Convert report.json from verdi rda binning tool outcome to a graphical representation
import json
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Patch

# 1) Load the JSON report
with open("rda_report_multiple.json", "r", encoding="utf-8") as f:
    report = json.load(f)  # :contentReference[oaicite:2]{index=2}

# 2) Build a flat list of (file, cluster_id)
rows = []
for bucket in report["bucket"]:
    cid   = bucket["id"]
    cases = bucket["cases"]
    for path in cases:
        # Extract filename from path
        fname = path.split("/")[-1]
        rows.append({"file": fname, "cluster": cid})

df = pd.DataFrame(rows)

# 3) Bar chart: cluster sizes
cluster_sizes = df["cluster"].value_counts().sort_index()
plt.figure(figsize=(8, 4))
cluster_sizes.plot(kind="bar", color="C0", edgecolor="k")
plt.xlabel("Cluster ID")
plt.ylabel("Number of Files")
plt.title("Cluster Sizes from Multiple Error Binning")
plt.xticks(rotation=0)
plt.tight_layout()
plt.show()

# 4) Scatter by cluster with jitter and annotations
plt.figure(figsize=(10, 3))
y = np.random.normal(loc=0, scale=0.1, size=len(df))  # small vertical jitter

scatter = plt.scatter(
    df["cluster"], y,
    c=df["cluster"], cmap="tab10",
    s=80, edgecolor="k", alpha=0.8
)

#add this baseline
#plt.axhline(0, color='black', linewidth=0.8, linestyle='-')

scatter = plt.scatter(
    df["cluster"], y,
    c=df["cluster"], cmap="tab10",
    s=80, edgecolor="k", alpha=0.8
)

# 1) draw the horizontal baseline
plt.axhline(0, color='black', linewidth=0.8, linestyle='-')

# 2) add the manual legend
from matplotlib.patches import Patch
ax = plt.gca()
unique_clusters = sorted(df["cluster"].unique())
cmap = plt.get_cmap("tab10")
legend_handles = [
    Patch(facecolor=cmap(c % 10),
          edgecolor="white",
          label=f"Cluster {c}",
          linewidth=0.8)
    for c in unique_clusters
]
ax.legend(
    handles=legend_handles,
    title="Cluster ID",
    bbox_to_anchor=(1.02, 1),
    loc="upper left",
    frameon=True
)

#3) then annotate points as before
# for i, row in df.iterrows():
#     plt.text(
#         row["cluster"], y[i] + 0.02, row["file"],
#         fontsize=7, rotation=45,
#         ha="right", va="bottom", alpha=0.7
#     )

plt.yticks([])  # hide the yâ??axis
plt.xlabel("Cluster ID")
plt.title("Files Grouped by Cluster (with jitter)")
plt.tight_layout()
plt.show()
