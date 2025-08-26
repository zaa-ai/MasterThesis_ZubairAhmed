# project_env.csh: project environment setup script
# call "project [m17402a] check" to check project structure and update project information
# ————————————————————————
# Initialize Environment Modules
# ————————————————————————

module use /common/department/design/tools/digitalDesignFlow/modules

# common project variables
setenv PROJECT_VERSION     verdi_eval
setenv PROJECT_STATE       $PROJECT_VERSION
setenv PROJECT_REPOSITORY  P52144
setenv PROJECT_NUMBER      52144
setenv PROJECT_DIR         `pwd`
setenv DESIGN              $PROJECT_DIR
setenv DIGITAL             DIGITAL
#Add extra directory to define workroot
setenv WORKROOT     $DIGITAL

# load modules
module unload designflow
module load designflow/develop
#module load designflow/2020.07

#module unload xa
#module load xa/M-2017.03

module unload vcs
#module load vcs/U-2023.03-1
module load vcs/S-2021.09-1
#module load vcs/R-2020.12-1
#module load vcs/T-2022.06-SP1

module unload icc
module load icc/S-2021.06-SP5-2

module unload gate_counter
module load  gate_counter/2022.04

module unload fm
module load fm/S-2021.06-SP5 

module unload tetramax
module load tetramax/U-2022.12-SP2

module unload lc
module load lc/S-2021.06-SP5

module unload dc
module load dc/S-2021.06-SP5-1

module unload icv
module load icv/S-2021.06-SP3-2

module unload pt
module load pt/S-2021.06-SP5 

module unload starrc
module load starrc/O-2018.06-SP5-2

module unload git
module load git

#module unload cx
#module load cx/O-2018.09

module unload xilinx
module unload vivado
module load vivado/2019.2

module unload spyglass
module load spyglass/T-2022.06-SP2

module unload verdi
module load verdi/U-2023.03-1

module unload euclide
module load euclide/Euclide-2023.03

module unload stove
module load stove/develop

module unload eugene
module load eugene/1.1.0

module unload meridian_cdc
module load meridian_cdc
module unload meridian_rdc
module load meridian_rdc
module unload idebug
module load idebug

#load verdi environment
#setenv SNPSLMD_LICENSE_FILE 27020@license03:27020@aedlmgr

# simulation flow environment
setenv SYNOPSYS_SIM_SETUP ${PROJECT_DIR}/synopsys_sim.setup
setenv UVM_HOME            $VCS_HOME/etc/uvm-1.2
setenv SIM_DIR             /nfs/wrk.${USER}/sim/${PROJECT_NUMBER}/${PROJECT_STATE}
setenv SIMDIR               $SIM_DIR
alias testcase "setenv TESTCASE"

# backend flow environment
setenv MCMM                1
setenv ELAB                1
setenv CORNER              ""
setenv TOP_MODULE          digtop
setenv PROJ_ROOT           $DESIGN/$DIGITAL
setenv PROJECT_HOME        $DESIGN/$DIGITAL
setenv TECHLIB             $DESIGN/$DIGITAL/tech
setenv PROCESS             tcb018gbwp7t
#prepends getPrjCfg.rb to $PATH variable for backend flow
module use $PROJECT_HOME/scripts
module load mod.scripts

#SVUnit
module load svunit

setenv FSDB_ENABLE_EXPAND_CLASS 1
setenv FSDB_VARIANT_SIZE_ARRAY 1
setenv VERDI_ENHANCE_DYNAMIC_OBJECT 1
setenv UVM_MESSAGE_LENGTH_LIMIT 0

alias si 'sim clean gen all -f -gui \!*'
alias sb 'sim clean gen all -f \!*'
alias sia 'setenv SEQUENCE_NAME \!:1 ; sim clean gen all -f -gui sim/any_sequence'
alias sba 'setenv SEQUENCE_NAME \!:1 ; sim clean gen all -f sim/any_sequence'
alias sra 'setenv SEQUENCE_NAME \!:1 ; sim run -gui -f sim/any_sequence'
alias sil 'sim clean gen all -f -gui -lay=config/digtop_signoff.config \!*'
alias sbl 'sim clean gen all -f -lay=config/digtop_signoff.config \!*'
alias srr 'sim -f \!*'

 #make sure to chmod rda_analysis.sh file to make it executable
if ( ! -x "$WORKROOT/rda_analysis.sh" ) then
    chmod u+x "$WORKROOT/rda_analysis.sh"
endif

###############################
# set prompt
###############################
set prompt = "%{\033[1;35m%}($PROJECT_VERSION)%{\033[0m%}%B%n@%m%b%{\033[0m%}%/>%b"
#####################################################################################
 
