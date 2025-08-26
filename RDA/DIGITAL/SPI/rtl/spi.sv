/**
 * Module: spi
 *
 * SPI module
 */
module spi import project_pkg::*; import buffer_if_pkg::*;
	#(
		parameter ADDR_WIDTH = 16
	) (
		clk_reset_if.slave      clk_rst,
		spi_int_if.slave        spi_int,
		elip_full_if.master     elip_spi_read,
		buffer_writer_if.master command_writer,
		buffer_reader_if.master dsi3_pdcm_data_reader,
		buffer_reader_if.master dsi3_crm_data_reader,
		spi_status_if.spi       spi_status,
		elip_if.slave           elip_registers,
		input	logic           i_clear_command_queue,
		input	logic			i_write_not_allowed,
        input   data_t          i_tdma_frame_word_count[DSI_CHANNELS-1:0],
        input   logic           i_ram_initialized,
        input   logic           i_set_command_ignored,
		output	elip_data_t     o_elip_data_read,
		output	dsi_select_t    o_dsi3_pdcm_data_read_channel_select,
		output	dsi_select_t    o_dsi3_crm_data_read_channel_select,
		output	logic           o_interrupt,
		ecc_error_if.master     spi_ecc_error,
		ecc_error_if.master     data_reader_ecc_error
	);
	
    ecc_error_if ecc_error_rx_data ();
    ecc_error_if spi_core_ecc_error ();
    
    assign  spi_ecc_error.single_error = ecc_error_rx_data.single_error | spi_core_ecc_error.single_error;
    assign  spi_ecc_error.double_error = ecc_error_rx_data.double_error | spi_core_ecc_error.double_error;
    
	import spi_implementation_pkg::*;
	
	data_ecc_t rx_data, rx_data_sync, tx_data;
	
	logic	tx_data_available, tx_data_available_synced, tx_data_taken_over, tx_data_taken_over_synced, rxd_valid;
	
	logic	command_in_pending, command_in_pending_synced;
	logic	received_word;
	
	logic	hardware_fail;
	logic	crc_error, command_incomplete;
    
    logic   set_command_ignored;
    logic   alignment_error, alignment_error_sync;
    logic   reset_received, reset_received_sync;
    logic   expect_command_nibble, expect_command_nibble_sync;
    spi_command_e   command_nibble;
	
	/*###   Registers   ######################################################*/
	`include "SPI_registers_if_inst.sv"
	SPI_registers #(
		.base_addr (BASE_ADDR_SPI),
		.addr_width(ADDR_WIDTH   )
	) i_SPI_registers (
		.clk_rst                   (clk_rst                   ),
		.addr                      (elip_registers.addr       ),
		.data_in                   (elip_registers.data_write ),
		.wr                        (elip_registers.wr         ),
		.rd                        (elip_registers.rd         ),
		.data_out                  (o_elip_data_read          ),
		.SPI_registers_SPI_IRQ_STAT(SPI_registers_SPI_IRQ_STAT.master),
		.SPI_registers_SPI_IRQ_MASK(SPI_registers_SPI_IRQ_MASK.master),
		.SPI_registers_STATUS_WORD (SPI_registers_STATUS_WORD.master ));
	
	assign	SPI_registers_SPI_IRQ_STAT.HW_FAIL_in = 1'b1;
	assign	SPI_registers_SPI_IRQ_STAT.CMD_INC_in = 1'b1;
	assign	SPI_registers_SPI_IRQ_STAT.CRC_ERR_in = 1'b1;
	assign	SPI_registers_SPI_IRQ_STAT.ALI_ERR_in = 1'b1;
	assign	SPI_registers_SPI_IRQ_STAT.CMD_IGN_in = 1'b1;
	
	assign	SPI_registers_SPI_IRQ_STAT.HW_FAIL_set = hardware_fail;
	assign	SPI_registers_SPI_IRQ_STAT.CMD_INC_set = command_incomplete;
	assign	SPI_registers_SPI_IRQ_STAT.CRC_ERR_set = crc_error;
    assign  SPI_registers_SPI_IRQ_STAT.ALI_ERR_set = alignment_error_sync;
	assign	SPI_registers_SPI_IRQ_STAT.CMD_IGN_set = set_command_ignored | i_set_command_ignored;
	
	assign	o_interrupt = |(SPI_registers_SPI_IRQ_STAT.value & SPI_registers_SPI_IRQ_MASK.value);
	
	/*###   IC status word   ######################################################*/
	STATUS_WORD_t ic_status;
	assign	ic_status.unused_1 = '0;
	assign  ic_status.HE  = spi_status.hardware_error | SPI_registers_SPI_IRQ_STAT.HW_FAIL | spi_status.hardware_fail;
	assign	ic_status.BF  = spi_status.buffer_fill_warning;
	assign	ic_status.PD  = spi_status.dsi3_pdcm_data_available;
	assign	ic_status.CR  = spi_status.dsi3_crm_data_available;
	assign	ic_status.NT  = spi_status.no_tdma_scheme_defined;
    assign  ic_status.CRC = SPI_registers_SPI_IRQ_STAT.CRC_ERR;
    assign  ic_status.SCE = SPI_registers_SPI_IRQ_STAT.ALI_ERR | SPI_registers_SPI_IRQ_STAT.CMD_INC | SPI_registers_SPI_IRQ_STAT.CMD_IGN;
	
	assign	SPI_registers_STATUS_WORD.BF_in = spi_status.buffer_fill_warning;
	assign	SPI_registers_STATUS_WORD.HE_in = ic_status.HE;
	assign	SPI_registers_STATUS_WORD.PD_in = spi_status.dsi3_pdcm_data_available;
	assign	SPI_registers_STATUS_WORD.CR_in = spi_status.dsi3_crm_data_available;
	assign	SPI_registers_STATUS_WORD.CRC_in = ic_status.CRC;
	assign	SPI_registers_STATUS_WORD.SCE_in = ic_status.SCE;
	assign	SPI_registers_STATUS_WORD.NT_in = ic_status.NT;
	
	/*###   core   ######################################################*/
	spi_core i_spi_core (
		.spi_i                                (spi_int                            ),
		.clk_rst                              (clk_rst                            ),
		.i_tx_data_available_synced           (tx_data_available_synced           ),
		.i_tx_data                            (tx_data                            ),
		.i_status_word                        (ic_status                          ),
		.i_command_running                    (command_in_pending_synced          ),
        .i_expect_command_nibble              (expect_command_nibble_sync         ),
        .i_command_nibble                     (command_nibble                     ),
		.o_txd_en_clear                       (tx_data_taken_over                 ),
		.o_data_received                      (rx_data                            ),
		.o_rxd_valid                          (rxd_valid                          ),
        .ecc_error                            (spi_core_ecc_error.master          ),
        .o_alignment_error                    (alignment_error                    ),
        .o_reset_received                     (reset_received                     )
    );
	
	/*###   sync   ######################################################*/
	spi_sync i_spi_sync (
		.clk_rst                          (clk_rst                               ),
		.i_spi_clk                        (spi_int.sck                           ),
		.i_tx_data_available              (tx_data_available                     ),
		.o_tx_data_available_synced       (tx_data_available_synced              ),
        .i_expect_command_nibble          (expect_command_nibble                 ),
        .o_expect_command_nibble          (expect_command_nibble_sync            ),
		.i_command_in_pending             (command_in_pending                    ),
		.o_command_in_pending_synced      (command_in_pending_synced             ),
		.i_tx_data_taken_over             (tx_data_taken_over                    ),
		.o_tx_data_taken_over_edge        (tx_data_taken_over_synced             ),
		.i_rxd_valid                      (rxd_valid                             ),
		.o_rxd_valid_edge                 (received_word                         ),
        .i_rx_data                        (rx_data                               ),
        .o_rx_data                        (rx_data_sync                          ),
        .i_alignment_error                (alignment_error                       ),
        .o_alignment_error_edge           (alignment_error_sync                  ),
        .i_reset_received                 (reset_received                        ),
        .o_reset_received_edge            (reset_received_sync                   )
    );
	
	/*###   FIFO   ######################################################*/
	data_ecc_t  fifo_data;
	logic	set_fifo_data, fifo_full;
    logic   some_tx_data_in_fifo;
    logic   clear_fifo;
	
	spi_tx_fifo #(
		.reset_value({16'hf1f1,ecc_t'(ECC_pkg::DWF_ecc_gen_chkbits(16, 6, 2048'hf1f1))})
	) i_spi_tx_fifo (
		.clk_rst         (clk_rst                   ),
		.i_fifo_data     (fifo_data                 ),
		.i_set_fifo_data (set_fifo_data             ),
		.i_pop_data      (tx_data_taken_over_synced ),
		.i_reset         (reset_received_sync | clear_fifo),
		.o_data_available_for_core(tx_data_available),
        .o_some_data_in_fifo (some_tx_data_in_fifo  ),
		.o_full          (fifo_full                 ),
		.o_data          (tx_data                   ));
	
	spi_fsm i_spi_fsm (
		.clk_rst                             (clk_rst                             ),
		.elip_spi_read                       (elip_spi_read                       ),
		.command_writer                      (command_writer                      ),
		.dsi3_pdcm_data_reader               (dsi3_pdcm_data_reader               ),
		.dsi3_crm_data_reader                (dsi3_crm_data_reader                ),
		.spi_status                          (spi_status                          ),
		.data_reader_ecc_error               (data_reader_ecc_error               ),
		.ecc_error_rx_data                   (ecc_error_rx_data.master            ),
		.i_clear_command_queue               (i_clear_command_queue               ),
		.i_write_not_allowed                 (i_write_not_allowed                 ),
		.i_fifo_full                         (fifo_full                           ),
        .i_some_tx_data_in_fifo              (some_tx_data_in_fifo                ),
		.i_received_word                     (received_word                       ),
		.i_rx_data                           (rx_data_sync                        ),
        .i_tx_data_available                 (tx_data_available                   ),
        .i_no_tdma_scheme_defined            (spi_status.no_tdma_scheme_defined   ),
        .i_reset_command_received            (reset_received_sync                 ),
        .i_alignment_error                   (alignment_error_sync                ),
        .i_tdma_frame_word_count             (i_tdma_frame_word_count             ),
        .i_ram_initialized                   (i_ram_initialized                   ),
		.o_dsi3_pdcm_data_read_channel_select(o_dsi3_pdcm_data_read_channel_select),
		.o_dsi3_crm_data_read_channel_select (o_dsi3_crm_data_read_channel_select ),
		.o_fifo_data                         (fifo_data                           ),
		.o_set_fifo_data                     (set_fifo_data                       ),
        .o_clear_fifo                        (clear_fifo                          ),
		.o_command_in_pending                (command_in_pending                  ),
		.o_crc_error                         (crc_error                           ),
		.o_hardware_fail                     (hardware_fail                       ),
		.o_command_incomplete                (command_incomplete                  ),
        .o_expect_command_nibble             (expect_command_nibble               ),
        .o_command_nibble                    (command_nibble                      ),
        .o_set_command_ignored               (set_command_ignored                 )
    );
	
endmodule
