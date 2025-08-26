+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
+incdir+${SYNOPSYS}/dw/sim_ver
${UVM_HOME}/src/uvm_pkg.sv
${UVM_HOME}/src/vcs/uvm_custom_install_vcs_recorder.sv

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut/
+incdir+${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_sram_bist/uvm_environment/
+incdir+${DESIGN}/${DIGITAL}/edf_registers

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/test_addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_pkg.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_sram_bist/unit_test_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_bus_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/elip_if.sv
${DESIGN}/${DIGITAL}/rtl/elip_full_if.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_error_if.sv

// Modules
${DESIGN}/${DIGITAL}/edf_registers/SRAM_BIST_registers.sv
${DESIGN}/${DIGITAL}/tech/TSMC_180_BCD/ip/SRAM_3072X23U18/lib/models/SRAM_3072X23U18.v
${SYNOPSYS}/dw/sim_ver/DW_ecc.v
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_decoder.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_encoder.sv

${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/ram_wrapper_ecc_with_bist.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_sram_bist/sram_bist_test.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_sram_bist/testsuite.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_sram_bist/testrunner.sv
