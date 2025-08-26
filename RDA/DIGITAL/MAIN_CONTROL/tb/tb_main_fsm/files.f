+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
${UVM_HOME}/src/uvm_pkg.sv
${UVM_HOME}/src/vcs/uvm_custom_install_vcs_recorder.sv
+incdir+${SYNOPSYS}/dw/sim_ver/

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/rtl
+incdir+${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm
+incdir+${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm/uvm_environment
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/common_lib_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/convert_queue.svh
${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm/unit_test_pkg.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm/jtag_tap_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/elip_if.sv
${DESIGN}/${DIGITAL}/rtl/elip_full_if.sv

// Modules
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/sync.sv
${DESIGN}/${DIGITAL}/tb/clk_rst_define.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_div.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_gen.sv
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_full_2_elip_bus.sv
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_bus_2_elip.sv
${DESIGN}/${DIGITAL}/model/ram_model.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm/test_top.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm/testrunner.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm/testsuite.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/tb/tb_main_fsm/main_fsm_test.sv
