// 
+setvar+DESIGN=$PROJECT_LOC
+setvar+DIGITAL=DIGITAL
-sverilog

+incdir+${SYNOPSYS}/dw/sim_ver/
+define+UVM_REG_PROTECTED_SAMPLE
+define+VCS

+incdir+${DESIGN}/${DIGITAL}/config
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_common_config_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_if_pkg.sv
${DESIGN}/${DIGITAL}/STD_COMPONENTS/RAM_ROM_LIB/hdl/bist_pkg.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_reader_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_writer_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/pdcm_buffer_writer_if.sv
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv

// Register Model
${DESIGN}/${DIGITAL}/tb_eugene/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/register_model.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/test_register_model.sv
${DESIGN}/${DIGITAL}/tb_eugene/registers/test_addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/epms/edf_epm_model_pkg.sv

${DESIGN}/${DIGITAL}/tb_eugene/dut/common_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/crc_calculation_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/common/common_env_pkg.svh

+incdir+${DESIGN}/${DIGITAL}/tb_eugene/dut
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/common/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/registers
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/epms
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/sequences
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/sequences/pattern_classes
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/sequences/sub_sequences
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/sequences/sub_sequences/ecc
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/sequences/sub_sequences/crm
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/sequences/sub_sequences/pdcm
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/sequences/sub_sequences/spec

${DESIGN}/${DIGITAL}/tb_eugene/sequences/pattern_classes/pattern_pkg.svh

+incdir+${DESIGN}/verification/pattern
+incdir+${DESIGN}/verification/pattern/ecps_simulation
${DESIGN}/verification/pattern/ecps_simulation/ecps_simulation_pkg.sv
${DESIGN}/verification/pattern/M52144A_pattern.sv

${DESIGN}/${DIGITAL}/tb_eugene/dut/OTP_model_if.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/sequence_if.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/clk_osc_if.sv
${DESIGN}/${DIGITAL}/model/TOP.sv
${DESIGN}/${DIGITAL}/model/dsi3_signal_converter_digital.sv
${DESIGN}/${DIGITAL}/tb_eugene/dut/TOP_wrapper.sv

+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/dsi3_slave_utilities
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/top/files.f
