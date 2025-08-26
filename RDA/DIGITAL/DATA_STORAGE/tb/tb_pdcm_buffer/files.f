+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
+incdir+${SYNOPSYS}/dw/sim_ver
+incdir+${DESIGN}/${DIGITAL}/ECC/rtl
${UVM_HOME}/src/uvm_pkg.sv
${UVM_HOME}/src/vcs/uvm_custom_install_vcs_recorder.sv
+incdir+${SYNOPSYS}/dw/sim_ver/

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_reader/
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/pdcm_buffer_writer/
+incdir+${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_pdcm_buffer/uvm_environment/
+incdir+${DESIGN}/${DIGITAL}/edf_registers

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_if_pkg.sv
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/test_addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common//common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_reader/buffer_reader_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/pdcm_buffer_writer/pdcm_buffer_writer_pkg.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_pdcm_buffer/unit_test_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_writer_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_reader_if.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/elip_bus_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/elip_if.sv
${DESIGN}/${DIGITAL}/rtl/elip_full_if.sv


// Modules
${DESIGN}/${DIGITAL}/model/ram_model.sv
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_bus_2_elip.sv
${DESIGN}/${DIGITAL}/tb/interface_converter_elip_full_2_elip_bus.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_pdcm_buffer/buffer_test.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_pdcm_buffer/testsuite.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/tb/tb_pdcm_buffer/testrunner.sv
