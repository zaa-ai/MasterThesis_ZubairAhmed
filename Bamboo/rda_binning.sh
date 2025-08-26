#!/bin/csh
# Load required environment modules
module use /common/department/design/tools/digitalDesignFlow/modules
source project_env.csh

# Load Verdi RDA module
module load verdi/W-2024.09-SP1  # This loads the Verdi RDA binning tool

# Set the Synopsys License Server
setenv SNPSLMD_LICENSE_FILE 27020@license03:27020@aedlmgr  # License server info

# Move to the DIGITAL directory
cd DIGITAL

# Generate the default RDA binning configuration file
autorca -gen_cfg_template temp.yaml -gen_mode binning

# Debugging: Print loaded modules and license
echo "Loaded modules:"
module list
echo "License file set to: $SNPSLMD_LICENSE_FILE"

# Ensure the config file exists before modifying
if (! -f temp.yaml) then
    echo "ERROR: temp.yaml was not created!"
    exit 1
endif

# Copy temp.yaml to rca.yaml for modification
cp temp.yaml rca.yaml

# Modify rca.yaml: Comment out user_defined_rule
sed -i 's/^\( *user_defined_rule: .*\)$/#\1/' rca.yaml

#move all the contents of failing logs into vcs.txt
find ./failing -type f -name "*.log" > vcs.txt

# Modify rca.yaml: Update latest_fail_list to use vcs.txt
sed -i 's|latest_fail_list: .*|latest_fail_list: ./vcs.txt|' rca.yaml

#run the binning file
autorca -cfg rca.yaml

# Debugging: Show modified configuration file
echo "Updated Configuration File:"
cat rca.yaml

# Print report.json content for verification
echo "Report File Contents:"
cat $BAMBOO_BUILD_WORKING_DIRECTORY/report.json
autorca -load_report report.json
# End of script
