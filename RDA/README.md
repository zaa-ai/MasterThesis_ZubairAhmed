# RDA Binning & Workflow

This repository contains the shell based (command line / terminal) scripts and Makefile needed to run RDA analysis and simulations as part of the thesis.

**Note:**
The complete project setup cannot be executed directly from the provided Git structure due to permission restrictions and Non-Disclosure Agreement (NDA) obligations.

As a workaround, only the source script used to automate the workflow has been included in this directory. These script represents the functional core of the implementation, while all proprietary or restricted components have been omitted in compliance with NDA requirements.
 
**Contact person:** thilo.schmidt@elmos.com
## Prerequisites

- **Bash** (with `set -euo pipefail` support)
- **GNU Make**
- Standard Unix utilities: `grep`, `xargs`, `find`, `mv`
- Access to the `autorca` tool liscence permission

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
### `run_all.sh`
This script provides a one-command workflow to clean the workspace, run regressions, perform RDA preprocessing, and then launch Verdi-related binning and debug steps. It stitches together GNU Make targets with the required Verdi environment setup (via C-shell).

1. **Ensure shell fails fast**
   ``(set -e)`` so any failing step aborts the pipeline

2. **Load environment modules**(sources ``/etc/profile.d/modules.sh`` if ``module`` isn’t already available)
3. **Invoke Make targets:**
   - ``make clean``
   - ``make clean_logs``
   - ``make regression``
4. **Initialize Verdi environment** and continue with Make:
- Spawns csh, sources ``./verdi.csh``, then runs:``
   - ``make rda_binning``
   - ``make debug``

**In short:** clean folders → logs clean → regressions → RDA prep → Verdi binning → debug, all chained together.
### `Makefile`
The Makefile provides simple build automation for the project:

- Defines rules for building targets, cleaning intermediate files, and running analysis steps.
- Encapsulates common workflows so you don’t have to re-enter long shell commands.
- Ensures reproducibility by re-running only the steps that need updating when files change.
- A timer can be set for the regression run so that the tests can terminate after timeout (watchdog timer)

Follow the steps in a sequence in order to run:
```bash 
cd 52144
source project_env.csh  # load project environment module
cd DIGITAL
source verdi.csh    # loads verdi rda modules
make  clean         # cleans the rda artifacts generated after the run
make  clean_logs    # cleans the generated logs
make  demo          # runs a sameple 15 error injected UVM log files(18 in total with passing logs), bins them, generates report and open GUI
```    

Other `make` commands with different function can be explored under:
```bash 
make  help  # to see all the available targets
```
This will display all the corresponding make commands that can be executed in the environment itself.

Some excerpts of other make commands:
```bash
make  tdma          # runs only one simulation titled 'upload_tdma' and generated UVM_ERROR log file
make  regression    # runs all tests in selected_test.list" with a timer
make  rda_analysis  # to run the rda_analysis.sh Workflow
make  rda_binning   # runs autorca and proceeds with binning and generate the rda_report.json
make  debug         # runs the rda_report.json file and opens GUI
```