# Bamboo Automated Integration 
Integrates an AI-enabled EDA tool 'Synopsys Verdi RDA' into the Atlassian -- Bamboo regression pipeline. This setup automates:
1. **Regression simulation** with VCS/UVM  
2. **AI-driven RDA “binning”** of fail logs with Verdi RDA Binning tool 
3. **HTML summary** of binning results  from .``json`` file

**Note:** The following setup has been fully integrated into Elmos’s regression system (Bamboo). Consequently, executing the visualization or simulation independently of the setup will not yield the intended outcomes. Nevertheless, the provided scripts can still be examined to gain a clear understanding of the underlying processes and system behavior.
## Table of Contents

- [Prerequisites](#prerequisites)  
- [Architecture & Workflow](#architecture--workflow)  
- [Installation & Setup](#installation--setup)  
- [Scripts](#scripts)  
  - [`regression.sh`](#regressionsh)  
  - [`rda_binning.sh`](#rda_binningsh)  
  - [`html_summary.sh`](#html_summarysh)  
- [Bamboo Job Configuration](#bamboo-job-configuration)  
- [Usage](#usage)  
- [Troubleshooting & FAQ](#troubleshooting--faq)  
- [Contributing](#contributing) 

---
**Direct Project link:** https://buildmaster1.elmos.de/browse/DIG52144-TEM3 

- Can be accessed by clicking the above link
- Make sure the plan branch is `verdi-rda-eval`
- Navigate to the `Actions` tab (top right)
- Select `Configure branch`
- From the top left menu, choose `RTL Simulations`
- All available `Script` can be found there

 

## Prerequisites

- **Bamboo**: Tested on Atlassian Bamboo ≥ 8.x  
- **Shell**: `/usr/local/bin/tcsh`, `/bin/csh`, and `bash` for Python snippet  
- **Synopsys VCS/UVM** and **Verdi RDA** installed as modules  
- **Python 3.6+** (for HTML summary script)  
- Environment modules under:
  ```text
  /common/department/design/tools/digitalDesignFlow/modules

- `project_env.csh` in your repo’s root to set:

    - `$DESIGN` → top-level design path

    - `$DIGITAL` → `$DESIGN/DIGITAL`

- Synopsys license server reachable via:

```bash
module load verdi/W-2024.09-SP1
export SNPSLMD_LICENSE_FILE=27020@license03:27020@aedlmgr
```
- Bamboo plan with a Checkout task that places your repo at `$BAMBOO_BUILD_WORKING_DIRECTORY`
## Architecture & Workflow:

1. `regression.sh`

    - Selects/filter tests from `regression.list`

    - Launches coverage-enabled simulations via `project sim cov`

    - Segregates passing vs. failing logs under `logs/`, `passing/`, `failing/`

    - Produces `vcs.txt` (list of failure logs) and `logs.tar.gz` as Artifact

2. `rda_binning.sh`

    - Loads Verdi RDA module for binning

    - Generates `temp.yaml`, transforms it to `rca.yaml` // Creating a copy of `temp.yaml` for reference

    - Inserts `vcs.txt` into `rca.yaml` → runs `autorca -cfg rca.yaml`

    - Outputs `rda_report.json` in the working directory

3. `html_summary.sh`

    - Reads `rda_report.json`

    - Emits an interactive `report_summary.html` for human review

## Installation & Setup
The original script has been executed in the Bamboo environment.

For analysis purpose, the below script setup shows how to do shell based execution.
```bash
# 1. Clone the repo
git clone --single-branch --branch develop https://gitea-int.elmos.de/DesignSupport/MasterThesis_VerdiRDA.git
cd Bamboo

# 2. Enable execution on your scripts
chmod +x scripts/*.sh

# 3. Ensure your `project_env.csh` exports:
#    DESIGN, DIGITAL, and any tool paths

# 4. (Optional) Install Python deps
pip3 install --user pyyaml
```
## Scripts
1. **`regression.sh`**

    - **Inputs:**

        - `regression.list` (test names)

        - `$DIGITAL/config/excludeList.el` (Optional)

    - **Outputs:**

        - `selected_test.list`, `vcs.txt`

        - `logs/`, `passing/`, `failing/`, `logs.tar.gz` (Artifact structure can be customized)

2. **`rda_binning.sh`**

    - **Inputs:**

        - `vcs.txt` from regression step

        - `temp.yaml` template

    - **Outputs:**

        - `rca.yaml` (final config)

        - `rda_report.json`

3. **`html_summary.sh`**

    - **Inputs:**

        - `DIGITAL/rda_report.json`

    - **Outputs:**

        - `DIGITAL/report_summary.html`


## Bamboo Job Configuration
1. Can be integrated alongside the working project.
2. No new changes has to be made in the original project setup.
3. The modules for Verdi RDA (in this setup) are loaded in the bash script.
## Usage
1. **Trigger manually** via Bamboo UI or commit to your regression branch.

2. **Inspect artifacts:**

    - `logs.tar.gz` → detailed VCS/UVM logs

    - `report_summary.html` → interactive binning summary

## Troubleshooting & FAQ
- **Module load failures**

    - Verify `module avail verdi/W-2024.09-SP1` succeeds.
    - If no, check liscence availibilty.

- **Empty** `selected_test.list`

    - Confirm your `regression.list` contains matching test names.

- `autorca` **errors**

    - Check `rca.yaml` exists and `vcs.txt` points to logs.

- **HTML missing buckets**

    - Ensure your JSON has `summary` and `bucket` keys.

## Contributing
1. Fork & branch off of `master`.

2. Add/update scripts and commit.

3. Submit a Pull Request describing your changes.