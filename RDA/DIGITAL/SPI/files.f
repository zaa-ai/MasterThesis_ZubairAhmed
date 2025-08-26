+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${SYNOPSYS}/dw/sim_ver/

//Packages 
${DESIGN}/${DIGITAL}/DATA_STORAGE/rtl/buffer_if_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_implementation_pkg.sv

//Interfaces
${DESIGN}/${DIGITAL}/SPI/rtl/spi_int_if.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_status_if.sv
${DESIGN}/${DIGITAL}/SPI/rtl/packet_reader_if.sv

//Modules
${DESIGN}/${DIGITAL}/SPI/rtl/buffer_writer_access_arbiter.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_error_buffer.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_core.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_sync.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_tx_fifo.sv
${DESIGN}/${DIGITAL}/SPI/rtl/crm_packet_reader.sv
${DESIGN}/${DIGITAL}/SPI/rtl/pdcm_frame_reader.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_tdma_reader_if.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_tdma_reader.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_fsm.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi.sv
