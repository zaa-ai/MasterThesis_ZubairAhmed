+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
${UVM_HOME}/src/uvm_pkg.sv

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/includes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/includes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/EASIER_UVM/tb
+incdir+${SYNOPSYS}/dw/sim_ver

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/digital_signal_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/spi_pkg.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/unit_test_pkg.sv

// Modules
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/otp_writer_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/flags_container_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/dsi3_packets_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/spi_protocol_listener_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/spi_sequences_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/crc_calculation_pkg_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/tdma_scheme_test.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/easier_uvm_testsuite.sv
${DESIGN}/${DIGITAL}/EASIER_UVM/tb/easier_uvm_testrunner.sv
