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
+incdir+${DESIGN}/${DIGITAL}/ECC/rtl
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_block
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_block/uvm_environment
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/includes/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_reader/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_writer/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_utilities/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/includes/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/includes/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_block/uvm_environment/

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/common_lib_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/digital_signal_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/register_model.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_reader/buffer_reader_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_writer/buffer_writer_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/dsi3_master_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/spi_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/convert_queue.svh
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_block/unit_test_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/elip_if.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/timebase_info_if.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_bus_if.sv

${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_writer_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_reader_if.sv
${DESIGN}/${DIGITAL}/rtl/elip_full_if.sv

${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_if.sv

// Modules
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/sync.sv
${DESIGN}/${DIGITAL}/tb/clk_rst_define.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_div.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_gen.sv
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_full_2_elip_bus.sv
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_bus_2_elip.sv
${DESIGN}/${DIGITAL}/model/ram_model.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_block/testrunner.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_block/testsuite.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_block/dsi3_block_test.sv
