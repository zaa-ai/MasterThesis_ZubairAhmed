
rm -rf csrc/ simv* ucli.key 

vcs -R +incdir+$SYNOPSYS/dw/sim_ver -pvalue+width=28 -pvalue+chkbits=8 DW_ecc_chk_eqs.sv -sverilog

