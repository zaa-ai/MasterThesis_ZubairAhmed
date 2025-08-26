setenv TESTCASE dsi3_crm_fpga
setenv UVM_TESTCASE top_test
setenv ANALYZE_OPTIONS "$ANALYZE_OPTIONS +define+target_technology_FPGA"
setenv ANALYZE_OBJECTS "tech/TSMC_180_BCD digtop_fpga model tb_eugene"
#setenv ANALYZE_OBJECTS	"tech/XILINX_UNISIM digtop_fpga model tb_eugene"
setenv ELAB_OPTIONS "$ELAB_OPTIONS -top glbl +charge_decay +neg_tchk +sdfverbose -sdf max:top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top:$DESIGN/$DIGITAL/FPGA/be_run/results/gate_lvl_netlist/fpga_fast.sdf "
setenv TC_DESCRIPTION "Basic testcase for command response mode with FPGA netlist" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,p52144_215_seq -top glbl"
setenv GATE_LEVEL ""
# do not forget the newline at the end
