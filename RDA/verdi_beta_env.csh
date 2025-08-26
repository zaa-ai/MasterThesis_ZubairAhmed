# source this file to use the Verdi Beta

module unload vcs
module load vcs/U-2023.03-1

module unload verdi
setenv VERDI_HOME /common/run/synopsys/verdi/verdi_TD-20230803
setenv PATH $VERDI_HOME/bin:$PATH

# beta license feature
setenv FLEXLM_DIAGNOSTICS 4
setenv ELMOS_SNPS_NONPROD 1
setenv TRANSACTION_IN_WAVE_WINDOW 1
