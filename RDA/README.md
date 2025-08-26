# RDA Binning & Workflow

This repository contains the scripts and Makefile needed to run RDA analysis and simulations as part of the MasterThesis_VerdiRDA project.

## Prerequisites

- **Bash** (with `set -euo pipefail` support)
- **GNU Make**
- Standard Unix utilities: `grep`, `xargs`, `find`, `mv`
- Access to the `autorca` tool liscence permission.

## Installation
```bash 
git clone --single-branch --branch verdi-rda-eval https://gitea-int.elmos.de/ds-digital/52144.git   #in work directory 
```
## Automation Scripts

### `rda_analysis.sh`
This shell script automates preparation and configuration for RDA (Root Cause Analysis):

1. **Copies simulation logs**  
   Reads test names from `selected_test.list`, finds each test’s `simulation.log`, and renames it as `<test>.log`.

2. **Separates passing and failing logs**  
   - Logs **without `UVM_ERROR`** → moved into `passing/`  
   - Logs **with `UVM_ERROR`** → moved into `failing/`

3. **Generates a fail list**  
   All failing logs are listed into `vcs.txt`.

4. **Creates an RDA configuration file**  
   Uses `autorca` to generate a template config (`temp.yaml`), copies it to `rca.yaml`, and tweaks it:
   - Comments out `user_defined_rule`  
   - Updates `latest_fail_list` to point to the newly created `vcs.txt`

This script ensures your RDA run always uses the latest simulation outputs and failing tests
## Running
### `Makefile`
The Makefile provides simple build automation for the project:

- Defines rules for building targets, cleaning intermediate files, and running analysis steps.
- Encapsulates common workflows so you don’t have to re-enter long shell commands.
- Ensures reproducibility by re-running only the steps that need updating when files change.
- A timer can be set for the regression run so that the tests can terminate after timeout (watchdog timer)

Follow the steps in a sequence in order to run:
```bash 
cd MasterThesis_VerdiRDA/RDA
source project_env.csh
cd DIGITAL
make help           # to see all the available targets
    - demo          # runs a sameple 15 error injected UVM log files(18 in total), bins them, generates report and open GUI
    - tdma          # runs only one simulation titled 'upload_tdma' and generated UVM_ERROR log file
    - regression    # runs all tests in selected_test.list" with a timer
    - rda_analysis  # to run the rda_analysis.sh Workflow
    - rda_binning   # runs autorca and proceeds with binning and generate the rda_report.json
    - debug         # runs the rda_report.json file and opens GUI
    - clean         # cleans the rda artifacts generated after the run
    - clean_logs    # cleans the generated logs
