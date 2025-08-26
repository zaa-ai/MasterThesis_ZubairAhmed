/**
 * Module: dsi3
 *
 * DSI3 block
 */
module dsi3 import project_pkg::*; #(
		parameter ADDR_WIDTH = 16
		)(
			clk_reset_if.slave		clk_rst,
			buffer_reader_if.master	command_reader[DSI_CHANNELS-1:0],
			buffer_writer_if.master	crm_data_writer[DSI_CHANNELS-1:0],
            pdcm_buffer_writer_if.master	pdcm_data_writer[DSI_CHANNELS-1:0],

			elip_if.slave			elip_registers,
			output	elip_data_t		o_elip_data_read,
			elip_full_if.master		elip_tdma[DSI_CHANNELS-1:0],

			timebase_info_if.slave	time_base,

			dsi3_io_if.master		dsi3_io[DSI_CHANNELS-1:0],

			pad_int_if.master		syncb_pad,

			jtag_bus_if.slave		jtag_bus,
			tmr_dsi_if.master		tmr_dsi[DSI_CHANNELS-1:0],
			tmr_out_dsi_if.master	tmr_out_dsi[DSI_CHANNELS-1:0],
			output	jtag_dr_for_registers_t	o_jtag_dr,
			
			command_control_to_dsi3_if.slave	from_command_control,

			input	logic			i_ot,
			input	logic			i_vdsi_en,
			input	logic			i_enable_transceivers,
			input	dsi_logic_t		i_clear_crm_data_buffer,
			input	dsi_logic_t		i_clear_pdcm_data_buffer,
            input   logic           i_invalidate_tdma_schemes,

			output	dsi_logic_t		o_interrupt,							// Interrupt output for INTN

			output	dsi_logic_t		o_transmit_pending,
			output	logic			o_hardware_error,
			output	dsi_logic_t		o_hw_fail,
			output	dsi_logic_t		o_no_tdma_scheme_defined,
            output  data_t          o_tdma_frame_word_count[DSI_CHANNELS-1:0],
			
			ecc_error_if.master		ecc_error_cmd,
			ecc_error_if.master		ecc_error_data,
			ecc_error_if.master		ecc_error_tdma
		);
	
	import dsi3_pkg::*;

	dsi_logic_t		tx;

	elip_data_t		elip_data_out_common;
	elip_data_t		elip_data_out_block[DSI_CHANNELS-1:0];
	
	synchronization_if 			sync[DSI_CHANNELS-1:0] ();

	jtag_dr_for_registers_t		jtag_dr[DSI_CHANNELS-1:0];
	dsi3_common_config_if 		common_config ();
	dsi3_start_request_if 		request[DSI_CHANNELS-1:0]();

	dsi_logic_t		tmr_dig_prevent_deactivation;
	dsi3_pkg::dsi3_tx_dac_t		txd_shaped[DSI_CHANNELS-1:0];

	dsi_logic_t		hardware_error, hardware_error_irq;
	
	ecc_error_if 	int_ecc_error_cmd[DSI_CHANNELS-1:0] ();
	ecc_error_if 	int_ecc_error_data[DSI_CHANNELS-1:0] ();
	ecc_error_if 	int_ecc_error_tdma[DSI_CHANNELS-1:0] ();
	
	dsi_logic_t		sync_error;

	`include "common_DSI3_block_registers_if_inst.sv"
	common_DSI3_block_registers #(
			.base_addr                                    (BASE_ADDR_DSI_COMMON                               ),
			.addr_width                                   (ADDR_WIDTH                                         )
		) i_common_DSI3_block_registers (
			.clk_rst                                      (clk_rst                                            ),
			.addr                                         (elip_registers.addr                                ),
			.data_in                                      (elip_registers.data_write                          ),
			.wr                                           (elip_registers.wr                                  ),
			.rd                                           (elip_registers.rd                                  ),
			.data_out                                     (elip_data_out_common                               ),
			.common_DSI3_block_registers_DSI_ENABLE       (common_DSI3_block_registers_DSI_ENABLE.master      ),
			.common_DSI3_block_registers_DSI_CFG          (common_DSI3_block_registers_DSI_CFG.master         ),
			.common_DSI3_block_registers_DSI_TX_SHIFT     (common_DSI3_block_registers_DSI_TX_SHIFT.master    ),
			.common_DSI3_block_registers_SYNC_IDLE_REG    (common_DSI3_block_registers_SYNC_IDLE_REG.master   ),
			.common_DSI3_block_registers_CRM_TIME         (common_DSI3_block_registers_CRM_TIME.master        ),
			.common_DSI3_block_registers_CRM_TIME_NR      (common_DSI3_block_registers_CRM_TIME_NR.master     ));
	
	assign	common_config.bit_time = dsi3_bit_time_e'(common_DSI3_block_registers_DSI_CFG.BITTIME);
	assign	common_config.chip_time = common_DSI3_block_registers_DSI_CFG.CHIPTIME;
	assign	common_config.crc_enable = common_DSI3_block_registers_DSI_CFG.CRC_EN;
	assign	common_config.sync_pdcm = common_DSI3_block_registers_DSI_CFG.SYNC_PDCM;
	assign	common_config.tx_shift = common_DSI3_block_registers_DSI_TX_SHIFT.SHIFT;
	assign	common_config.timeout_crm = common_DSI3_block_registers_CRM_TIME.TIME;
	assign	common_config.timeout_crm_nr = common_DSI3_block_registers_CRM_TIME_NR.TIME;
	assign	o_hardware_error = |(hardware_error_irq);

	always_comb begin
		common_DSI3_block_registers_DSI_ENABLE.TRE_in = '0;
		common_DSI3_block_registers_DSI_ENABLE.TRE_set = 1'b0;
		if ((hardware_error & common_DSI3_block_registers_DSI_ENABLE.TRE) != '0) begin
			common_DSI3_block_registers_DSI_ENABLE.TRE_set = 1'b1;
			if (common_DSI3_block_registers_DSI_ENABLE.access_wr == 1'b1)
				common_DSI3_block_registers_DSI_ENABLE.TRE_in = ~(hardware_error & ~tmr_dig_prevent_deactivation) & (common_DSI3_block_registers_DSI_ENABLE.TRE | elip_registers.data_write[DSI_CHANNELS-1:0]);
			else
				common_DSI3_block_registers_DSI_ENABLE.TRE_in = ~(hardware_error & ~tmr_dig_prevent_deactivation) & common_DSI3_block_registers_DSI_ENABLE.TRE;
		end
		if ((i_vdsi_en == 1'b0) && (i_enable_transceivers == 1'b1)) begin
			common_DSI3_block_registers_DSI_ENABLE.TRE_set = 1'b1;
			common_DSI3_block_registers_DSI_ENABLE.TRE_in = '0;
		end
		if (i_ot == 1'b1) begin
			common_DSI3_block_registers_DSI_ENABLE.TRE_set = 1'b1;
			common_DSI3_block_registers_DSI_ENABLE.TRE_in = '0;
		end
	end
	assign	from_command_control.dsi3_enabled = common_DSI3_block_registers_DSI_ENABLE.TRE;

	/*###   start management - synchronization and start time   ######################################################*/
	dsi3_start_manager i_dsi3_start_manager (
		.clk_rst          (clk_rst                                          ), 
		.common_config    (common_config.slave                              ), 
		.request          (request.slave                                    ), 
		.sync             (sync.slave                                       ), 
		.syncb_pad        (syncb_pad                                        ), 
		.i_register_sync  (from_command_control.register_sync               ), 
        .i_sync_master    (common_DSI3_block_registers_DSI_CFG.SYNC_MASTER  ),
        .i_tick_1us       (time_base.tick_1us                               ),
		.o_sync_error     (sync_error                                       ), 
		.o_syncb          (common_DSI3_block_registers_SYNC_IDLE_REG.PIN_in ));
	
	/*###   DSI3 block   ######################################################*/
	dsi3_io_if dsi3_io_block[DSI_CHANNELS-1:0] ();
    
	generate
		for (genvar i=0; i<DSI_CHANNELS; i++) begin : generate_dsi3_blocks

			dsi3_block #(
					.BASE_ADDR                          (BASE_ADDR_DSI[i]                  ),
					.BASE_ADDR_TRIMMING                 (BASE_ADDR_DSI_TRIMMING[i]         ),
					.ADDR_WIDTH                         (ADDR_WIDTH                        ),
					.BASE_ADDR_TEST                     (BASE_ADDR_TEST_DSI[i]             ),
					.BASE_ADDR_TDMA                     (BASE_ADDR_DSI_TDMA[i]             ),
					.CHANNEL                            (i                                 )
				) i_dsi3_block (
					.clk_rst                                 (clk_rst                           ),
					.command_reader                          (command_reader[i]                 ),
					.pdcm_data_writer                        (pdcm_data_writer[i]               ),
					.crm_data_writer                         (crm_data_writer[i]                ),
					.elip_registers                          (elip_registers                    ),
					.o_elip_register_read                    (elip_data_out_block[i]            ),
					.elip_tdma                               (elip_tdma[i]                      ),
					.dsi3_io                                 (dsi3_io_block[i].dsi3_block       ),
					.common_config                           (common_config.dsi3_block          ),
					.time_base                               (time_base                         ),
					.sync                                    (sync[i].master                    ),
					.request                                 (request[i].master                 ),
					.i_transceiver_enable                    (common_DSI3_block_registers_DSI_ENABLE.TRE[i] & i_enable_transceivers),
					.ecc_error_cmd                           (int_ecc_error_cmd[i].master       ),
					.ecc_error_data                          (int_ecc_error_data[i].master      ),
                    .ecc_error_tdma                          (int_ecc_error_tdma[i].master      ),
					.i_clear_crm_data_buffer                 (from_command_control.clear_crm_data_buffer[i] | i_clear_crm_data_buffer[i]),
					.i_clear_pdcm_data_buffer                (from_command_control.clear_pdcm_data_buffer[i] | i_clear_pdcm_data_buffer[i]),
					.i_clear_and_invalidate_crm_data_buffer  (i_clear_crm_data_buffer[i]        ),
					.i_clear_and_invalidate_pdcm_data_buffer (i_clear_pdcm_data_buffer[i]       ),
					.i_stop_transmission                     (from_command_control.stop_transmission[i]),
                    .i_set_command_error                     (from_command_control.set_command_error[i]),
                    .i_invalidate_tdma_scheme                (i_invalidate_tdma_schemes         ),
					.o_interrupt                             (o_interrupt[i]                    ),
					.o_transmit_pending                      (o_transmit_pending[i]             ),
					.o_hard_ware_error                       (hardware_error[i]                 ),
					.o_hard_ware_error_irq                   (hardware_error_irq[i]             ),
					.jtag_bus                                (jtag_bus                          ),
					.tmr_dsi                                 (tmr_dsi[i]                        ),
					.tmr_out_dsi                             (tmr_out_dsi[i]                    ),
					.i_sync_error                            (sync_error[i] | from_command_control.set_sync_error[i] ),
					.o_jtag_dr                               (jtag_dr[i]                        ),
					.o_tmr_dig_prevent_deactivation          (tmr_dig_prevent_deactivation[i]   ),
					.o_busy                                  (common_DSI3_block_registers_SYNC_IDLE_REG.DSI_in[i]),
					.o_hw_fail                               (o_hw_fail[i]                      ),
					.o_clear_command_queue                   (from_command_control.clear_command_queue[i]),
					.o_no_tdma_scheme_defined                (o_no_tdma_scheme_defined[i]       ),
                    .o_tdma_frame_word_count                 (o_tdma_frame_word_count[i]        )
				);

			// assignment of TxD to vector for waveshaping
			assign	tx[i] = dsi3_io[i].tx;
			assign	dsi3_io[i].txd_shaped = txd_shaped[i];
			assign	dsi3_io[i].bit_time = common_config.bit_time;
			
			assign	dsi3_io_block[i].rx  = dsi3_io[i].rx;
			assign	dsi3_io_block[i].ov  = dsi3_io[i].ov;
			assign	dsi3_io_block[i].uv  = dsi3_io[i].uv;
			assign	dsi3_io_block[i].i_q = dsi3_io[i].i_q;
			
			assign	dsi3_io[i].rx_idac = dsi3_io_block[i].rx_idac;
			assign	dsi3_io[i].tx = dsi3_io_block[i].tx;
			assign	dsi3_io[i].tx_hvcasc_on = dsi3_io_block[i].tx_hvcasc_on;
			assign	dsi3_io[i].tx_on = dsi3_io_block[i].tx_on;
			assign	dsi3_io[i].rx_on = dsi3_io_block[i].rx_on;
			assign	dsi3_io[i].receive_mode_enable = dsi3_io_block[i].receive_mode_enable;
			assign	dsi3_io[i].trim_rx1 = dsi3_io_block[i].trim_rx1;
			assign	dsi3_io[i].trim_rx2 = dsi3_io_block[i].trim_rx2;
			
			assign	ecc_error_cmd.double_error[i]  = int_ecc_error_cmd[i].double_error;
			assign	ecc_error_cmd.single_error[i]  = int_ecc_error_cmd[i].single_error;
			assign	ecc_error_data.double_error[i] = int_ecc_error_data[i].double_error;
			assign	ecc_error_data.single_error[i] = int_ecc_error_data[i].single_error;
			assign	ecc_error_tdma.double_error[i]  = int_ecc_error_tdma[i].double_error;
			assign	ecc_error_tdma.single_error[i]  = int_ecc_error_tdma[i].single_error;
            
			
			always_comb begin
				if (common_DSI3_block_registers_DSI_CFG.CHIPTIME == CHIPTIME_2US)
					dsi3_io[i].short_filter_time = 1'b1;
				else 
					dsi3_io[i].short_filter_time = 1'b0;
			end
		end
	endgenerate

	always_comb begin
		o_jtag_dr = '0;
		foreach(jtag_dr[i]) begin
			o_jtag_dr |= jtag_dr[i];
		end
	end

	dsi3_wave_shaping #(
			.DSI_COUNT	(DSI_CHANNELS)
		) i_wave_shaping (
			.clk_rst   (clk_rst),
			.jtag_bus  (jtag_bus),
			.i_tx      (tx),
			.i_tx_bit_time(common_config.bit_time),
			.o_tx_dac  (txd_shaped)
		);

	always_comb begin
		o_elip_data_read =  elip_data_out_common;
		for (int k=0; k<DSI_CHANNELS; k++) begin
			o_elip_data_read |= elip_data_out_block[k];
		end
	end

endmodule
