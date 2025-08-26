+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/rtl
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${SYNOPSYS}/dw/sim_ver/
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_tdma_buffer/uvm_environment/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/test_addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_pkg.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/common_lib_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_tdma_buffer/unit_test_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_writer_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_reader_if.sv
${DESIGN}/${DIGITAL}/rtl/pad_int_if.sv
${DESIGN}/${DIGITAL}/rtl/elip_full_if.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/OTP_model_if.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_if.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/tdma_interface.sv

// Modules
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_div.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_gen.sv
${DESIGN}/${DIGITAL}/model/ram_model.sv
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_full_2_elip_bus.sv
${DESIGN}/${DIGITAL}/tb/clk_rst_define.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_tdma_buffer/test.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_tdma_buffer/testrunner.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_tdma_buffer/testsuite.sv
