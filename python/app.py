# Requirements:
# pip install streamlit pandas numpy scikit-learn hdbscan matplotlib

import os
import tempfile
import numpy as np
import pandas as pd
import streamlit as st
import logging
# Suppress verbose caching manager logs
logging.getLogger("streamlit.runtime.caching").setLevel(logging.WARNING)
import hdbscan
from scipy.sparse import hstack
from sklearn.cluster import KMeans
from sklearn.decomposition import TruncatedSVD
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics import adjusted_rand_score, adjusted_mutual_info_score, silhouette_score
from sklearn.preprocessing import StandardScaler
import matplotlib.pyplot as plt
import re
import string

# ---------- Text Cleaning ----------
def clean_text(t: str) -> str:
    """Normalize text: split letters/numbers, lowercase, remove punctuation."""
    t = re.sub(r'(?<=[A-Za-z])(?=[0-9])', ' ', t.lower())
    t = re.sub(r'(?<=[0-9])(?=[A-Za-z])', ' ', t)
    return t.translate(str.maketrans('', '', string.punctuation))

# ---------- Data Loading & Preprocessing ----------
@st.cache_data(show_spinner=False)
def load_logs_from_folder(folder_path: str):
    logs = []
    for fname in os.listdir(folder_path):
        if fname.endswith(".log"):
            with open(os.path.join(folder_path, fname), 'r', encoding='utf-8', errors='ignore') as f:
                logs.append((fname, f.read()))
    return logs

@st.cache_data(show_spinner=False)
def extract_structured_features(logs):
    UVM_LOG_PATTERN = re.compile(r"(?P<severity>UVM_INFO|UVM_WARNING|UVM_ERROR|UVM_FATAL)\s+@\s+(?P<time>[0-9\.]+)us:\s+\[(?P<module>[^\]]+)\]\s+(?P<message>.+)")
    CONFIG_PATTERN = re.compile(r"\+(?P<key>UVM_TESTNAME|uvm_set_type_override|UVM_VERBOSITY)=(?P<value>[\w\.\-]+)")
    SIM_WARNING_PATTERN = re.compile(r"(Null object access|constraint solver failure|Segmentation fault|coverage illegal hit)", re.IGNORECASE)
    records = []
    for fname, txt in logs:
        for line in txt.splitlines():
            m = UVM_LOG_PATTERN.match(line)
            if m:
                records.append({'file': fname, 'severity': m.group('severity'), 'time_us': float(m.group('time')), 'module': m.group('module'), 'message': m.group('message')})
                continue
            mc = CONFIG_PATTERN.search(line)
            if mc:
                records.append({'file': fname, 'severity': '', 'time_us': 0.0, 'module': 'CONFIG', 'message': f"{mc.group('key')}={mc.group('value')}"})
                continue
            ms = SIM_WARNING_PATTERN.search(line)
            if ms:
                records.append({'file': fname, 'severity': 'SIM_ERROR', 'time_us': 0.0, 'module': 'SIM', 'message': ms.group(1)})
    df = pd.DataFrame(records)
    feats = []
    for fname, grp in df.groupby('file'):
        d = {'file': fname}
        counts = grp['severity'].value_counts().to_dict()
        for sev in ['UVM_INFO','UVM_WARNING','UVM_ERROR','UVM_FATAL','SIM_ERROR']:
            d[f'count_{sev}'] = counts.get(sev, 0)
        d['unique_modules'] = grp['module'].nunique()
        d['total_messages'] = len(grp)
        errs = grp[grp.severity=='UVM_ERROR']
        d['first_error_time'] = errs.time_us.min() if not errs.empty else 0.0
        d['last_error_time'] = errs.time_us.max() if not errs.empty else 0.0
        feats.append(d)
    df_struct = pd.DataFrame(feats).set_index('file').fillna(0)
    return df, df_struct

# ---------- TF-IDF & Hybrid Features ----------
@st.cache_data(show_spinner=False)
def vectorize_text(documents, stopwords, min_df, max_df, max_features):
    vect = TfidfVectorizer(preprocessor=clean_text,
                           stop_words=stopwords or None,
                           token_pattern=r"(?u)\b[a-z][a-z]{2,}\b",
                           ngram_range=(1,1), min_df=min_df, max_df=max_df,
                           max_features=max_features, sublinear_tf=True, norm='l2')
    X = vect.fit_transform(documents)
    return X, vect

#@st.cache_data(show_spinner=False)
def build_hybrid_features(_X_tfidf, df_struct, r_text, r_num):
    tfidf_scaled = StandardScaler(with_mean=False).fit_transform(_X_tfidf)
    struct_scaled = StandardScaler().fit_transform(df_struct.values)
    n_text, n_num = tfidf_scaled.shape[1], struct_scaled.shape[1]
    alpha, beta = np.sqrt(r_text/n_text), np.sqrt(r_num/n_num)
    return hstack([alpha*tfidf_scaled, beta*struct_scaled])

# ---------- SVD ----------
#@st.cache_data(show_spinner=False)
def run_svd(_hybrid, n_components):
    svd = TruncatedSVD(n_components=n_components, random_state=42)
    return svd.fit_transform(_hybrid), svd

# ---------- Clustering ----------
def cluster_hdbscan(Xred, params):
    return hdbscan.HDBSCAN(
        min_cluster_size=params['min_cluster_size'],
        min_samples=params['min_samples'],
        metric=params.get('metric', 'euclidean'),
        cluster_selection_method=params.get('cluster_selection_method', 'eom'),
        cluster_selection_epsilon=params.get('cluster_selection_epsilon', 0.0),
        allow_single_cluster=params.get('allow_single_cluster', False),
        alpha=params.get('alpha', 1.0)
    ).fit_predict(Xred)

def cluster_kmeans(Xred, k):
    km = KMeans(n_clusters=k, random_state=42)
    return km.fit_predict(Xred), km.cluster_centers_

# ---------- Plotting ----------
def plot_clusters(Xred, labels, filenames, algo, centers=None, show_centroids=False):
    fig, ax = plt.subplots(figsize=(8,6))
    ax.scatter(Xred[:,0], Xred[:,1], c=labels, s=50, alpha=0.8, edgecolor='k')
    if algo=='KMeans' and show_centroids and centers is not None:
        ax.scatter(centers[:,0], centers[:,1], marker='X', s=200, linewidths=2, edgecolor='white')
    ax.set(title=f"{algo} Clusters", xlabel='SVD 1', ylabel='SVD 2')
    for i, f in enumerate(filenames): ax.text(Xred[i,0], Xred[i,1], f, fontsize=6, alpha=0.7)
    return fig

# ---------- Streamlit App ----------
def main():
    st.title("UVM Log Clustering Explorer")
    with st.sidebar:
        st.header("Data Input")
        use_zip = st.checkbox("Upload logs as ZIP")
        if use_zip:
            z = st.file_uploader("ZIP of .log files", type='zip')
            if z:
                tmp = tempfile.TemporaryDirectory(); import zipfile
                zipfile.ZipFile(z).extractall(tmp.name)
                folder = tmp.name
            else:
                st.warning("Upload a ZIP file")
                return
        else:
            folder = st.text_input("Log Folder Path", 'failing_logs_52144')

        st.header("Preprocessing")
        ctx = st.number_input("Context lines", 0,10,0)
        extra_sw = st.text_area("Extra stopwords (comma sep)")
        sw = [w.strip() for w in extra_sw.split(',') if w.strip()]

        st.header("TF-IDF")
        min_df = st.slider("min_df",0.0,1.0,0.09)
        max_df = st.slider("max_df",0.0,1.0,0.6)
        max_feat = st.number_input("Max features",10,10000,1500)

        st.header("Hybrid & SVD")
        r_text = st.slider("Text ratio",0.0,1.0,0.85)
        r_num = 1.0-r_text
        n_comp = st.number_input("SVD components",2,10,2)

        st.header("Clustering")
        algo = st.selectbox("Algorithm",['HDBSCAN','KMeans'])
        if algo=='HDBSCAN':
            params = {
                'min_cluster_size': st.number_input("min_cluster_size",2,50,2),
                'min_samples': st.number_input("min_samples",0,50,1),
                'metric': st.selectbox("Metric", ['euclidean','manhattan','chebyshev']),
                'cluster_selection_method': st.selectbox("Selection method", ['eom','leaf']),
                'cluster_selection_epsilon': st.slider("epsilon",0.0,0.5,0.00),
                'allow_single_cluster': st.checkbox("Allow single cluster", False),
                'alpha': st.slider("alpha",0.1,2.0,0.8)
            }
        else:
            k_opt = st.selectbox("k or auto",['auto']+list(range(2,11)))

        y_file = st.file_uploader("True labels CSV", type='csv')
        df_true = pd.read_csv(y_file, index_col=0) if y_file else None

    # ---------- Pipeline ----------
    logs = load_logs_from_folder(folder)
    df_raw, df_struct = extract_structured_features(logs)
    docs, fnames = [], []
    for f,txt in logs:
        fnames.append(f)
        errs = [ln for ln in txt.splitlines() if 'UVM_ERROR' in ln]
        docs.append(' '.join(errs[:1+ctx]))

    X_tfidf, vect = vectorize_text(docs, sw, min_df, max_df, max_feat)
    hybrid = build_hybrid_features(X_tfidf, df_struct, r_text, r_num)
    Xred, svd = run_svd(hybrid, n_comp)

    if algo=='HDBSCAN':
        labels = cluster_hdbscan(Xred, params)
        centers = None
        display_params = params.copy()
    else:
        if k_opt=='auto':
            best_k, best_score = None, -1
            for k in range(2,11):
                lbl, ctr = cluster_kmeans(Xred, k)
                score = (adjusted_rand_score(df_true.values.ravel(), lbl) if df_true is not None else silhouette_score(Xred, lbl))
                if score > best_score: best_k, best_score = k, score
            labels, centers = cluster_kmeans(Xred, best_k)
            display_params = {'k': best_k}
        else:
            labels, centers = cluster_kmeans(Xred, int(k_opt))
            display_params = {'k': int(k_opt)}

    # ---------- Results Display ----------
    tab1, tab2, tab3, tab4 = st.tabs(["Plot","Metrics","Summary","Downloads"])
    with tab1:
        show_cent = st.checkbox("Show centroids", False)
        cols = st.columns([3,1])
        with cols[0]:
            st.pyplot(plot_clusters(Xred, labels, fnames, algo, centers, show_cent))
        with cols[1]:
            st.subheader("File Cluster Assignments")
            df_clusters = pd.DataFrame({'file': fnames, 'cluster': labels})
            df_clusters = df_clusters.sort_values('cluster').reset_index(drop=True)
            st.table(df_clusters)
    with tab2:
        metrics = {'Algorithm': algo,'Text_ratio':r_text,'Numeric_ratio':r_num, **display_params,
                   'ARI': (adjusted_rand_score(df_true.values.ravel(), labels) if df_true is not None else 'N/A'),
                   'AMI': (adjusted_mutual_info_score(df_true.values.ravel(), labels) if df_true is not None else 'N/A'),
                   'Silhouette': (silhouette_score(Xred[labels!=-1], labels[labels!=-1]) if algo=='HDBSCAN' and len(set(labels))>2 else silhouette_score(Xred, labels))}
        st.table(pd.DataFrame([metrics]))
    with tab3:
        df_summary = pd.DataFrame([(int(lbl),cnt) for lbl,cnt in pd.Series(labels).value_counts().items()], columns=['Cluster','Count'])
        df_summary['Percentage'] = df_summary['Count'].div(len(labels)).map("{:.1%}".format)
        st.table(df_summary)
    with tab4:
        df_raw.to_csv('uvm_log_structured.csv', index=False)
        st.download_button('Download Structured CSV','uvm_log_structured.csv')
        pd.DataFrame(X_tfidf.toarray(), index=fnames, columns=vect.get_feature_names_out()).to_csv('tfidf_features.csv')
        st.download_button('Download TF-IDF CSV','tfidf_features.csv')
        np.save('hybrid_features.npy', hybrid.toarray())
        st.download_button('Download Hybrid .npy','hybrid_features.npy')
        pd.DataFrame(svd.components_.T, index=list(vect.get_feature_names_out())+list(df_struct.columns), columns=[f'SVD{i+1}' for i in range(svd.n_components)]).to_csv('svd_loadings.csv')
        st.download_button('Download SVD Loadings','svd_loadings.csv')
        pd.DataFrame({'file':fnames,'cluster':labels}).to_csv('logs_clusters.csv', index=False)
        st.download_button('Download Cluster Assignments','logs_clusters.csv')

if __name__ == '__main__':
    main()
