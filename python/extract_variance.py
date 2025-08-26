
#Visualize the features extracted from the .csv file to show weights of each feature
import pandas as pd

# 1. Load the full TF-IDF data
df = pd.read_csv('tfidf_features.csv')

# 2. Identify the name of your document-ID column (often 'Unnamed: 0')
doc_col = df.columns[0]

# 3. Compute variance for all token columns (exclude the ID)
variances = df.drop(columns=doc_col).var()

# 4. Pick the top 20 tokens by descending variance
top20_tokens = variances.sort_values(ascending=False).head(20).index.tolist()

# 5. Create reduced DataFrame with ID + top 20 token columns
df_small = df[[doc_col] + top20_tokens]

# 6. Export to a new CSV
df_small.to_csv('tfidf_features_small.csv', index=False)

print("Exported tfidf_features_small.csv with columns:", [doc_col] + top20_tokens)

