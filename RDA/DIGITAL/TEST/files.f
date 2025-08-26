+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${SYNOPSYS}/dw/sim_ver/

//Packages 
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_tap_pkg.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_pkg.sv

//Interfaces
${DESIGN}/${DIGITAL}/TEST/rtl/clock_switch_if.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_pad_if.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_bus_if.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_status_if.sv
${DESIGN}/${DIGITAL}/TEST/rtl/tmr_scan_if.sv
${DESIGN}/${DIGITAL}/TEST/rtl/tmr_top_if.sv

//Modules
${DESIGN}/${DIGITAL}/TEST/rtl/sync_reset.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_tap.sv
${DESIGN}/${DIGITAL}/TEST/rtl/jtag_elip.sv
${DESIGN}/${DIGITAL}/TEST/rtl/test_control.sv
${DESIGN}/${DIGITAL}/TEST/rtl/test_top.sv
${DESIGN}/${DIGITAL}/TEST/rtl/test.sv
