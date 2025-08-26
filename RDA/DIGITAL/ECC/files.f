// includes
+incdir+${DESIGN}/${DIGITAL}/config/
+incdir+${DESIGN}/${DIGITAL}/ECC/rtl/
+incdir+${SYNOPSYS}/dw/sim_ver/

// packages
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_pkg.sv

// interfaces
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_error_if.sv

//Modules
${SYNOPSYS}/dw/sim_ver/DW_ecc.v
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_decoder.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_encoder.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_register.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_edge_detection.sv

