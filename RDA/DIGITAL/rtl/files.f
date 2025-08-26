// include directories
+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/rtl
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${SYNOPSYS}/dw/sim_ver/
+incdir+${DESIGN}/${DIGITAL}/ECC/rtl

// packages
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_if_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv

// interfaces
${DESIGN}/${DIGITAL}/rtl/elip_full_if.sv
//${DESIGN}/${DIGITAL}/rtl/pad_if.sv
${DESIGN}/${DIGITAL}/rtl/pad_int_if.sv
${DESIGN}/${DIGITAL}/rtl/command_control_to_dsi3_if.sv

// HDL files
${DESIGN}/${DIGITAL}/rtl/elip_splitter.sv
${DESIGN}/${DIGITAL}/rtl/control_command_buffer_clearing.sv
${DESIGN}/${DIGITAL}/rtl/command_control.sv
${DESIGN}/${DIGITAL}/rtl/pad_mux_test.sv
${DESIGN}/${DIGITAL}/rtl/pad_mux_test_jtag_inputs.sv
${DESIGN}/${DIGITAL}/rtl/spi_interface_generator.sv
${DESIGN}/${DIGITAL}/rtl/logic_top.sv
${DESIGN}/${DIGITAL}/rtl/digtop.sv
