+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
${UVM_HOME}/src/uvm_pkg.sv

+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/includes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/includes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/includes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_utilities
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/includes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut

+incdir+${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/uvm_environment
+incdir+${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames
+incdir+${SYNOPSYS}/dw/sim_ver

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/epms/edf_epm_model_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/digital_signal_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/dsi3_master_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/spi_pkg.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/spi_frames_unit_test_pkg.sv

// Modules
${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/spi_frames_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/behaviour_checker_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/tdma_scheme_upload_listener_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/dsi3_master_transmission_checker_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/spi_frames_testsuite.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb_spi_frames/spi_frames_testrunner.sv
