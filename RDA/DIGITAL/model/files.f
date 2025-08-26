+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${SYNOPSYS}/dw/sim_ver/

// packages
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv

// interfaces
${DESIGN}/${DIGITAL}/COMMON_LIB/rtl/clk_reset_if.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_int_if.sv
${DESIGN}/${DIGITAL}/model/OTP_model_if.sv

// HDL files
${DESIGN}/${DIGITAL}/model/clkref_filter.sv
${DESIGN}/${DIGITAL}/model/IO_DIN_DIG_gate.sv
${DESIGN}/${DIGITAL}/model/dsi_transceiver.sv
${DESIGN}/${DIGITAL}/model/dsi3_signal_converter_digital.sv
${DESIGN}/${DIGITAL}/model/ANA.sv
${DESIGN}/${DIGITAL}/TIMEBASE/models/osc_trim.sv
${DESIGN}/${DIGITAL}/TIMEBASE/models/osc_top.sv
${DESIGN}/${DIGITAL}/TIMEBASE/models/pll_top.sv
${DESIGN}/${DIGITAL}/model/supply_top.sv
${DESIGN}/${DIGITAL}/model/TOP.sv
