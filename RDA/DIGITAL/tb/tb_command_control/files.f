+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
${UVM_HOME}/src/uvm_pkg.sv
${UVM_HOME}/src/vcs/uvm_custom_install_vcs_recorder.sv
+incdir+${SYNOPSYS}/dw/sim_ver/
+incdir+${DESIGN}/${DIGITAL}/ECC/rtl

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/includes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_reader/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_writer/
+incdir+${DESIGN}/${DIGITAL}/tb/tb_command_control/uvm_environment
+incdir+${DESIGN}/${DIGITAL}/edf_registers

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_if_pkg.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_implementation_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/spi_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_reader/buffer_reader_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_writer/buffer_writer_pkg.sv
${DESIGN}/${DIGITAL}/tb/tb_command_control/unit_test_pkg.sv


// INTERFACES
${DESIGN}/${DIGITAL}/tb/tb_command_control/dsi_logic_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_writer_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_reader_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/rtl/elip_full_if.sv
${DESIGN}/${DIGITAL}/rtl/command_control_to_dsi3_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/elip_if.sv


// Modules
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_full_2_elip_bus.sv
${DESIGN}/${DIGITAL}/model/ram_model.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer.sv
${DESIGN}/${DIGITAL}/rtl/control_command_buffer_clearing.sv
${DESIGN}/${DIGITAL}/rtl/command_control.sv

${DESIGN}/${DIGITAL}/tb/tb_command_control/command_control_test.sv
${DESIGN}/${DIGITAL}/tb/tb_command_control/testsuite.sv
${DESIGN}/${DIGITAL}/tb/tb_command_control/testrunner.sv
