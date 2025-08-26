-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_reader/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/buffer_writer/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/digital_signal/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_master/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/dsi3_slave/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/elip_bus/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/jtag_master/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/osc/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/pdcm_buffer_writer/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/real_signal/files.f
-f ${DESIGN}/${DIGITAL}/tb_eugene/agents/spi/files.f

+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/top
+incdir+${DESIGN}/${DIGITAL}/tb_eugene/agents/top/includes
${DESIGN}/${DIGITAL}/tb_eugene/agents/top/top_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/top/top_test_pkg.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/top/top_th.sv
${DESIGN}/${DIGITAL}/tb_eugene/agents/top/top_tb.sv
