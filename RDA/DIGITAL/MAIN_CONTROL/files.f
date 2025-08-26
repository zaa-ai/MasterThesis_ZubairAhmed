// include directories
+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl
+incdir+${SYNOPSYS}/dw/sim_ver/

// packages
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/main_control_pkg.sv

// interfaces
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/supply_io_if.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/otp_ip_bus_if.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/otp_io_if.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/tmr_supply_if.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/tmr_out_supply_if.sv

// HDL files
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/ic_revision.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/otp_control.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/otp_reader.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/vcc_deb.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/main_fsm.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/main_control.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/test_supply.sv
${DESIGN}/${DIGITAL}/MAIN_CONTROL/rtl/romnibble.sv
