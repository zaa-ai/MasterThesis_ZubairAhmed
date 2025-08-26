# Log-Driven Clustering Pipeline

A glorified script that parses UVM log files, turns them into a mash-up of numeric and text features, and then slices and dices them into clusters with DBSCAN and K-Means—because apparently manually clustering error messages over a long list of failing UVM based log files takes long time.

Based on a couple of refrences, but most of the consideration and ideas are taken from [DVCON clustering algorithm.](https://dvcon-proceedings.org/wp-content/uploads/clustering-and-classification-of-uvm-test-failures-using-machine-learning-techniques.pdf)


## Table of Contents

1. [Prerequisites](#prerequisites)  
2. [Installation](#installation) 
    - [Running](#running) 
3. [Usage](#usage)  
4. [Algorithm Overview](#algorithm-overview)  
5. [Configuration & Hyperparameters](#configuration--hyperparameters)  
6. [Ground-Truth Benchmarking](#ground-truth-benchmarking)  
7. [Clustering & Visualization](#clustering--visualization)  
8. [Contributing](#contributing)  

---

## Prerequisites

– Python 3.8+  
– A mess of `.log` files in your `failing_logs_52144` folder  
– A strong coffee (optional but recommended)  

## Installation:
Installation can be done either on Conda environment or virtual environmnt in the local compiler.
1. **Virtual Environment (Visual code studio)**
- **Install the Python extension**
If you haven’t already, install Microsoft’s “Python” extension from the VS Code Marketplace.

- **Create a new virtual-env**

    - Open the Command Palette (`Ctrl+Shift+P`) → **Python: Create Environment**

    - Choose Venv and pick a folder (e.g. `.venv` in your workspace).

    - VS Code will create and activate the venv for you.
- **Install everything via pip**
    - In that same terminal (venv already active!), run:
```bash
pip install -r requirements.txt
```

- VS Code will pick up your `.venv` interpreter and you can just run/debug as usual.
2. **Conda Environemnt**
- Application downloaded from the Baramundi Kiosk.
- Anaconda Navigator 2.6.3 used for the environment setup   
```bash
dbscan_environment.yaml
```
- Upload the above `.yaml` file in your conda to create a new environemnt.
- Visual code studio used for the working and setup, other compilers can also be used.
## Running
- In order to run the algorithm, run the `streamlit run app.py` and the browser will open automatically.
- The default values are already been set, tune the paramters to see how the hyperparamters affects the clustering.
## Usage
```bash
python testing_15_updated.py 
```
By default it will:

1. Walk through `./failing_logs_52144/*.log` and Classify failing and passing log file

2. Parse UVM lines, config flags, simulator warnings

3. Extract structured counts & timings → CSV

4. Build one “document” per log (first UVM_ERROR ± context)

5. Vectorize with TF-IDF (**+ custom stopwords (Hardcoded)**) → `.npy` & CSV

6. Scale & weight text vs. numeric → hybrid feature matrix

7. Dimensionality reduction with Truncated SVD → 2D embedding

8. HDBSCAN hyper-parameter tuning (ARI vs. your manual “desired” map)

9. K-Means hyper-parameter tuning (ARI as well)

10. Print summaries, visualize clusters in two separate scatter plots

```bash
python testing_15.py 
```
By default it will:

1. Walk through `./failing_logs_52144/*.log` and Classify failing and passing log file

2. Parse UVM lines, config flags, simulator warnings

3. Extract structured counts & timings → CSV

4. Build one “document” per log (first UVM_ERROR ± context)

5. Vectorize with TF-IDF (**+ automatic stop words**) →  CSV

6. Scale & weight text vs. numeric → hybrid feature matrix

7. Dimensionality reduction with Truncated SVD → 2D embedding

8. HDBSCAN hyper-parameter tuning (ARI vs. your manual “desired” map)

9. K-Means hyper-parameter tuning (ARI as well)

10. Calculates PPV and outputs macro/micro ppv showing the hit and miss of logs in a bin

11. Print summaries, visualize clusters in two separate scatter plots

```bash
python Metrics_calculation.py 
```
By default it will:

1. Performs same steps as `testing_15_updated.py` 

2. Display in detail calculation (in Terminal) of the Evaluation Metrics (AMI,ARI and Silhoutte score)



## Algorithm Overview
1. **Pre-processing**

    -Regex for `UVM_INFO`, `UVM_WARNING`, `UVM_ERROR`, `UVM_FATAL` lines

    -Config flags (`+UVM_TESTNAME=…`, `+uvm_set_type_override=…`)

    -Simulator warnings (null access, segfaults, solver failures)

2. **Structured Features**
    -Counts of each severity level
    -Number of unique modules, total messages
    -Timestamps of first & last UVM_ERROR

3. **Text Features (TF-IDF)**
    -One document per log: first error message ± context
    -Lowercase, split alphanumeric blobs, strip punctuation
    -Custom stopword list of log junk
    -Vectorize → sparse TF-IDF matrix

4. **Hybrid Feature Matrix**
    -**Scale** both blocks to unit variance
    -**Weight** them (text vs. numeric) via tunable α / β
    -**Concatenate** into one big feature array
5. **Dimensionality Reduction**
    -Truncated SVD → 2 components
    -2D embedding for visual inspection & clustering
6. **Clustering & Hyperparameter Tuning**
    -**HDBSCAN**
        -Grid-search `eps` ∈ [0.1,1.0], `min_samples` ∈ {2…6}
        -Optimize Adjusted Rand Index vs. your `desired` mapping
    -**K Means**
        -Grid-search `k` ∈ {2…10} (or restrict to your known group count)
        -Same ARI metric
7. **Reporting & Visualization**
-Terminal summary: cluster sizes, noise %, silhouette, ARI
-Two colored scatter plots (DBSCAN & K-Means) with legend
-Optional text box overlay of counts & ARI on the figure

**Note:** The algorithm only considers the first `UVM_ERROR` and clusters the logs files accordingly. Multiple lines (after the first `UVM_Error`) could also be selected by setting `context_lines` values bigger than 0, where each number represent the number of lines.
```python
def create_document_per_log(df, context_lines=0):
```


## Configuration & Hyperparameters
**Log folder:**
Adjust `LOG_FOLDER` at the top according to your needs in order to see how the clustering is happening.

**TF-IDF:**
-`ngram_range=(1,2)`
-`max_df=0.8, min_df=2, max_features=1000`
-Custom stopwords in `custom_stopwords`

**Hybrid weights:**
-`alpha` (text weight), `beta` (numeric weight)
-To force 50/50 variance:

```python

n_text, n_num = tfidf_scaled.shape[1], struct_scaled.shape[1]
alpha = 1/np.sqrt(n_text)
beta  = 1/np.sqrt(n_num)
```
-To use a 40/60 split:

```python
r_text, r_num = 0.4, 0.6
alpha = np.sqrt(r_text / n_text)
beta  = np.sqrt(r_num  / n_num)
```
**HDBSCAN grid:**
-`eps` from 0.1 to 1.0 (40 steps)
-`min_samples` ∈ [2,3,4,5,6]
**K-Means grid:**
-`k` ∈ [2…10] (or restrict around your true count)
## Ground-Truth Benchmarking
The core purpose of this part is for the evaluation of the framework with the manual baseline (ground truth)
To achieve this, define your “ideal” clusters once in the script:

```python
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
```
The script then computes:

```python
y_true = np.array([ desired.get(fname, -1) for fname in documents.index ])
```
and evaluates both DBSCAN and K-Means hyperparameters against this mapping using `sklearn.metrics.adjusted_rand_score`.

This part of the code and the corresponding can later be commented out.
*A clean code is still in process*:)

## Clustering & Visualization
After tuning:

**HDBSCAN**

-Fit with best (`eps, min_samples`) → `labels`

-Print counts, `%`, silhouette (if ≥2 clusters)

-Scatter colored by `labels`, legend, and summary textbox

**K-Means**

-Fit with best `k` → `km_labels`

-Similar summary + silhouette

-Separate colored scatter plot

All plots are generated with Matplotlib; you can swap colormaps (e.g. `Set2`, `Dark2`, `tab20`) to spice up the visualization.

## Contributing
Pull and push requests are actually welcomed (yes, really), but please follow the guidelines so there isn't a mess :)

