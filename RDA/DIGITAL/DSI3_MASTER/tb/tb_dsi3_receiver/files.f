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
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/uvm_environment
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/uvm_environment/slave_timing
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_utilities/.
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/includes/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/data
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/sequences/
+incdir+${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/uvm_environment/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal

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
${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/dsi3_master_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave//dsi3_slave_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/digital_signal_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/spi_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/register_model.sv
//${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/uvm_environment/slave_timing/m52142a_slave_timing.svh
//${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/uvm_environment/slave_timing/m52142b_slave_timing.svh
${DESIGN}/${DIGITAL}/tb_eugene/common/convert_queue.svh
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/unit_test_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_if.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_common_config_if.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_if.sv

// Modules
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/sync.sv
${DESIGN}/${DIGITAL}/tb/clk_rst_define.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_div.sv
${DESIGN}/${DIGITAL}/TIMEBASE/rtl/tick_gen.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_chip_converter.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_chip_filter_counter.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_filter.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_receive_filter.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_receive_counter.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_receive_sample_counter.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_receive_sampling.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_receive_data_collect.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_symbol_builder.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_symbol_lut.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_receive.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/testrunner.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/testsuite.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/chip_conversion_rx_to_chip.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/dsi3_filter_test.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/tb/tb_dsi3_receiver/dsi3_receiver_test.sv
