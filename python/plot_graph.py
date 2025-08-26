
# To plot clustering graph for the python framework
# works for both the algorithms, HDBSCAN and K means
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

# 1. Load the full TF-IDF data
df = pd.read_csv('tfidf_features.csv',index_col=0)

# 1) Heatmap
plt.figure()
plt.imshow(df.values, aspect='auto')
plt.colorbar()
plt.xticks(range(len(df.columns)), df.columns, rotation=90)
plt.yticks(range(len(df.index)), df.index)
plt.title('TFâ?"IDF Heatmap')
plt.xlabel('Tokens')
plt.ylabel('Log Documents')
plt.tight_layout()
#plt.savefig('/mnt/data/tfidf_heatmap.png')
plt.show()
<
# 2) Bar Graph of Average TF-"IDF per Token
avg_scores = (df.mean(axis=0)*100).sort_values(ascending=False)

plt.figure(figsize=(12, 6))
bars = plt.bar(avg_scores.index, avg_scores.values, edgecolor='black')

# Color mapping: use a colormap to shade bars by value
tnorm = plt.Normalize(avg_scores.min(), avg_scores.max())
colors = plt.cm.viridis(tnorm(avg_scores.values))
for bar, color in zip(bars, colors):
    bar.set_facecolor(color)

# Annotate each bar with its value
def annotate_bars(bars):
    for bar in bars:
        height = bar.get_height()
        plt.text(bar.get_x() + bar.get_width()/2, height + 0.01,
                 f'{height:.2f}', ha='center', va='bottom', fontsize=8)

annotate_bars(bars)

plt.xticks(rotation=45, ha='right', fontsize=9)
plt.ylabel('Average TFâ?"IDF Score', fontsize=12)
plt.title('Average TFâ?"IDF per Token', fontsize=14)
plt.grid(axis='y', linestyle='--', alpha=0.7)
plt.tight_layout()
plt.show()
#plt.savefig('/mnt/data/tfidf_bar.png')  # save after display


# Purity for each cluster
correct = [66.66] + [100]*13
incorrect = [100 - c for c in correct]
clusters = np.arange(1, 15)

plt.figure(figsize=(10, 4))
# Plot the â??correctâ?? portion
plt.bar(clusters, correct, label='Correctly Binned', color='tab:green')
# Plot the â??incorrectâ?? portion on top
plt.bar(clusters, incorrect, bottom=correct, label='Misâ??binned', color='tab:red')

plt.xticks(clusters)
plt.ylim(0, 110)
plt.xlabel('Cluster ID')
plt.ylabel('Percentage')
plt.title('Cluster Purity Breakdown')
plt.legend(loc='upper right')
plt.tight_layout()
plt.show()
