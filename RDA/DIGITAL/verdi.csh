# verdi.csh: project environment setup script
# ————————————————————————
# Initialize Environment Modules
# ————————————————————————
module use /common/department/design/tools/digitalDesignFlow/modules

module unload verdi/U-2023.03-1
module load verdi/W-2024.09-SP1  

#load verdi environment
setenv SNPSLMD_LICENSE_FILE 27020@license03:27020@aedlmgr

# Feedback to user (or sad developer)
echo "Verdi environment successfully loaded: verdi/W-2024.09-SP1"
echo "SNPSLMD_LICENSE_FILE set to $SNPSLMD_LICENSE_FILE(EVAL Liscence)"