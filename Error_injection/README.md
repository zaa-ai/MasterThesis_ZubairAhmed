# UVM error log files

This directory contains the dataset of UVM error-injected log files that serve as the baseline for evaluation in the thesis

## File Structure
- ``UVM_Error_log_files`` : Directory containing all UVM error–induced log files
- ``30_uvm_error_with_meaning.xlsx`` : Excel workbook documenting UVM error information
## Contents
- ``UVM_Error_log_files`` : Log files generated after simulating the RTL code with systematically injected errors. These logs provide the detailed information required to perform error binning using the different algorithms described in the thesis
- ``30_uvm_error_with_meaning.xlsx`` : Ground-truth baseline created manually. This file includes the rationale for each binning category, along with metadata such as the testcase name, module information, and the meaning of the injected error


