+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
+incdir+${SYNOPSYS}/dw/sim_ver

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/rtl
+incdir+${DESIGN}/${DIGITAL}/ECC/tb/tb_ecc_register
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/common_lib_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv

// Modules
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/sync.sv
${DESIGN}/${DIGITAL}/tb/clk_rst_define.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_div.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_gen.sv
${DESIGN}/${DIGITAL}/ECC/tb/tb_ecc_register/testrunner.sv
${DESIGN}/${DIGITAL}/ECC/tb/tb_ecc_register/testsuite.sv
${DESIGN}/${DIGITAL}/ECC/tb/tb_ecc_register/ecc_register_test.sv
