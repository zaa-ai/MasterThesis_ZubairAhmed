+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/ECC/rtl
+incdir+${SYNOPSYS}/dw/sim_ver/

// PACKAGES
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_if_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/ECC/rtl/ecc_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_reader_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_writer_if.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/pdcm_buffer_writer_if.sv

// Modules
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_reader_demux.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_writer_demux.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/pdcm_buffer.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffers.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/elip_full_to_elip.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/elip_system_arbiter.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/elip_ram_access_arbiter.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/ram_wrapper_ecc_with_bist.sv
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/data_storage.sv
