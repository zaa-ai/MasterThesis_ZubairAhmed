setenv TESTCASE register_access_fpga
setenv ANALYZE_OPTIONS "$ANALYZE_OPTIONS +define+target_technology_FPGA"
setenv ANALYZE_OBJECTS	"tech/TSMC_180_BCD digtop_fpga model tb_easier_uvm"
setenv ELAB_OPTIONS "$ELAB_OPTIONS -top glbl +charge_decay +neg_tchk +sdfverbose -sdf max:top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top:$DESIGN/$DIGITAL/FPGA/be_run/results/gate_lvl_netlist/fpga_fast.sdf "
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "testcase with fpga netlist for master register access" 
setenv VCS_OPTIONS "$VCS_OPTIONS +uvm_set_type_override=top_default_seq,register_access_seq -top glbl"
# do not forget the newline at the end
