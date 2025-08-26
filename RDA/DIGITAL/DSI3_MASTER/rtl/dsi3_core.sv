/**
 * Module: dsi3_core
 *
 * DSI3 core master module consisting of transmitter and receiver
 */
module dsi3_core import project_pkg::*; import dsi3_pkg::*; import buffer_if_pkg::*; (
		// interfaces
		clk_reset_if.slave	clk_rst,									// system clock with its reset

		input	logic[1:0]	i_rx,
		output	logic		o_tx,

		dsi3_common_config_if.dsi3_block	common_config,
		timebase_info_if.slave				time_base,
        pdcm_buffer_writer_if.master		pdcm_data_writer,
		buffer_writer_if.master				crm_data_writer,
        tdma_reader_if.master               tdma_reader,
		
		DSI3_channel_registers_PACKET_STAT_if.slave	DSI3_channel_registers_PACKET_STAT,
		DSI3_channel_registers_FRAME_STAT_if.slave	DSI3_channel_registers_FRAME_STAT,

		// inputs
		input	logic		i_uv,
		input	logic		i_ov,

		input	logic		i_transceiver_enable,
		input   data_ecc_t  i_data_high,
		input   data_ecc_t  i_data_low_crc,
		input	logic		i_start,
		input	logic		i_broad_cast,
		input	channel_mode_t	i_mode,
		input	logic		i_clear_crm_data_buffer,
		input	logic		i_clear_pdcm_data_buffer,
		input	logic		i_clear_and_invalidate_crm_data_buffer,
		input	logic		i_clear_and_invalidate_pdcm_data_buffer,
		input	logic		i_pdcm_receive_timeout,
        input   logic       i_stop,

		//outputs
        `ifdef VCS
        output  data_t      o_current_time_in_period,
        `endif
		output	logic		o_acknowledge_start,
		output	logic		o_finished,
		output	logic		o_transmit_pending,
		output	logic		o_receive_mode_enable,
		ecc_error_if.master	ecc_error_cmd,
		ecc_error_if.master	ecc_error_data,
		output	logic[1:0]	o_rx_test,
		output	logic[1:0]	o_rx_filtered,
		output	logic		o_hw_fail,
		output	logic[3:0]	o_slaves,
		output	logic		o_dm_overflow,
        output  data_t      o_data_high_ecc_corrected,
        output  data_t      o_data_low_ecc_corrected
	);
	
	logic			hw_fail_transceive_fsm, hw_fail_crm_data_fsm, hw_fail_pdcm_data_fsm;
	assign			o_hw_fail = hw_fail_crm_data_fsm | hw_fail_transceive_fsm | hw_fail_pdcm_data_fsm;
	
	logic[3:0]		slaves_next;
	logic			set_slaves;
	
	channel_mode_t	mode, mode_next;
	
    general_data_writer_inputs_if general_data_writer_inputs ();
	
	logic	chip_in_filtered, filter_en;
	logic	sensed_new_slave;
	assign	sensed_new_slave = ((chip_in_filtered == 1'b1) && (o_slaves != 4'hf)) ? 1'b1 : 1'b0;
	logic	clear_flag_for_received_packets;
	logic	received_at_least_one_packet;
	
	logic[8:0]		cnt_dm, cnt_dm_nxt;
	logic			cnt_dm_en;
    
    logic   transceiver_enable_previous;
    logic   received_c0_after_packet;

	
	/*###   ECC_DECODER - data path to dsi3 transmitter  ######################*/
	logic[DATA_WIDTH-1:0] data_high_ecc_corrected;
	logic high_data_ecc_fail;
	logic high_data_ecc_corr;

	ecc_decoder #(
			.DATA_WIDTH  (DATA_WIDTH),
			.ECC_WIDTH   (ECC_WIDTH)
		) i_ecc_dec_data_high_dsi3_trm (
			.i_correct_n (1'b0),
			.i_data      (i_data_high.data),
			.i_ecc       (i_data_high.ecc),
			.o_data      (data_high_ecc_corrected),
			.o_ecc_cor   (high_data_ecc_corr),
			.o_ecc_err   (high_data_ecc_fail)
		);

	logic[DATA_WIDTH-1:0] data_low_ecc_corrected;
	logic	low_data_ecc_fail, low_data_ecc_corr;
	ecc_error_if #(.WIDTH (1)) transmitter_data_ecc_error ();

	ecc_decoder #(
			.DATA_WIDTH  (DATA_WIDTH),
			.ECC_WIDTH   (ECC_WIDTH)
		) i_ecc_dec_data_low_dsi3_trm (
			.i_correct_n (1'b0),
			.i_data      (i_data_low_crc.data),
			.i_ecc       (i_data_low_crc.ecc),
			.o_data      (data_low_ecc_corrected),
			.o_ecc_cor   (low_data_ecc_corr),
			.o_ecc_err   (low_data_ecc_fail)
		);

	assign ecc_error_cmd.double_error = high_data_ecc_fail | low_data_ecc_fail | transmitter_data_ecc_error.double_error;
	assign ecc_error_cmd.single_error = high_data_ecc_corr | low_data_ecc_corr | transmitter_data_ecc_error.single_error;
    
    assign o_data_high_ecc_corrected = data_high_ecc_corrected;
    assign o_data_low_ecc_corrected  = data_low_ecc_corrected;

	/*###   Transmitter   ######################################################*/
	logic		acknowledge_start;
	logic		transmit_pending;
    logic       start_transmit;

	logic[31:0]	data_for_transmit;
	always_comb begin
		case (i_mode)
			MODE_PDCM:	data_for_transmit = 32'h7fff_ffff;
			MODE_DM:	data_for_transmit = 32'h1fff_ffff;
			default:	data_for_transmit = {data_high_ecc_corrected, data_low_ecc_corrected};
		endcase
	end
	dsi3_transmit i_dsi3_transmit (
			.clk_rst                 (clk_rst                ),
			.i_data                  (data_for_transmit      ),
			.i_mode                  (i_mode                 ),
			.i_start                 (start_transmit         ),
			.i_bit_time				 (common_config.bit_time ),
			.i_enable                (i_transceiver_enable   ),
			.o_pend                  (transmit_pending       ),
			.o_tx                    (o_tx                   ),
			.o_receive_mode_enable	 (o_receive_mode_enable  ),
			.o_sample_time_base		 (general_data_writer_inputs.start_transmit),
			.o_acknowledge_start     (acknowledge_start	     ),
			.ecc_error               (transmitter_data_ecc_error.master)
		);

	assign	o_transmit_pending = transmit_pending;

	/*###   Receiver   ######################################################*/
	logic	rec_enable;
	timebase_t	receive_time_out_crm;
	timebase_t	time_of_start_transmit;
	timebase_t	time_of_start_receive;
	logic	sample_receive_start_time;

	logic	handle_receive_time_out, handle_receive_time_out_next;
	logic	store_empty_packet;
    logic   crm_receive_timeout;
    logic   receive_time_out_tick_crm, receive_time_out_tick_pdcm;
    
    `ifdef VCS
     assign o_current_time_in_period = time_base.base_time - time_of_start_transmit;
    `endif

	typedef enum logic[3:0] {DSI_IDLE, TRANSMIT, RECEIVE, DM_SETUP, DM_WAIT_FOR_PULSE, DM_PULSE, DM_WAIT_FOR_SLAVE, DM_WAIT_FOR_NEXT, DM_CHECK_SLAVE} dsi_state_enum;
	dsi_state_enum	dsi_state, dsi_state_nxt;
	
	always_comb begin
		handle_receive_time_out_next = handle_receive_time_out;
        receive_time_out_tick_crm = 1'b0;
        receive_time_out_tick_pdcm = 1'b0;
		if ((mode == MODE_CRM) && (dsi_state == RECEIVE))begin
            if (crm_receive_timeout == 1'b1)
                receive_time_out_tick_crm = time_base.tick_1us;
		end
		else begin
			receive_time_out_tick_pdcm = i_pdcm_receive_timeout;
		end
	end
	
    always_comb begin
        if((time_base.base_time - time_of_start_transmit) > receive_time_out_crm)
            crm_receive_timeout = 1'b1;
        else
            crm_receive_timeout = 1'b0;
    end

	dsi3_receive i_dsi3_receive (
			.clk_rst                    (clk_rst                                          ),
			.i_enable_receiver          (rec_enable                                       ),
			.i_rx                       (i_rx                                             ),
			.i_sample_cfg               (common_config.chip_time                          ),
			.i_receive_time_out         (receive_time_out_tick_crm | receive_time_out_tick_pdcm ),
			.o_rx_test                  (o_rx_test                                        ),
			.o_data                     (general_data_writer_inputs.rx_data               ),
			.o_symbol_count             (general_data_writer_inputs.symbol_count          ),
			.o_rec_pending	            (general_data_writer_inputs.rec_pending           ),
			.o_symbol_error_set         (general_data_writer_inputs.symbol_error_set      ),
			.o_received_data            (general_data_writer_inputs.received_data         ),
			.o_response_finished        (general_data_writer_inputs.response_finished     ),
			.o_symbol_count_overflow    (general_data_writer_inputs.symbol_count_overflow ),
			.o_receiving_started_tick   (sample_receive_start_time                        ),
			.o_received_c0_after_packet (received_c0_after_packet                         ),
			.o_rx_filtered              (o_rx_filtered                                    ));
    
	/*###   DM timebase   ######################################################*/
    logic   tick_1us;
    tick_div #(.ratio(18)) i_tick_1us (
        .clk_rst   (clk_rst   ),
        .tick_in   (cnt_dm_en ),
        .reset_sync(1'b0      ),
        .tick_out  (tick_1us  )
    );
    
	/*###   FSM   ######################################################*/
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			dsi_state		<= DSI_IDLE;
			time_of_start_transmit       <= '0;
			time_of_start_receive        <= '0;
            receive_time_out_crm         <= '0;
			mode                         <= MODE_CRM;
			handle_receive_time_out      <= 1'b0;
			o_slaves                     <= '0;
			cnt_dm                       <= '0;
            transceiver_enable_previous  <= '0;
		end
		else begin
			dsi_state		<= dsi_state_nxt;
			if (general_data_writer_inputs.start_transmit == 1'b1) begin
				time_of_start_transmit	<= time_base.base_time;
                if ((i_broad_cast == 1'b1) && (i_mode == MODE_CRM)) 
                    receive_time_out_crm <= {5'd0, common_config.timeout_crm_nr};
                else
                    receive_time_out_crm <= {5'd0, common_config.timeout_crm};
            end
			if (sample_receive_start_time == 1'b1)
				time_of_start_receive	<= time_base.base_time;
			mode			<= mode_next;
			handle_receive_time_out <= handle_receive_time_out_next;
            transceiver_enable_previous <= i_transceiver_enable;
			if (set_slaves == 1'b1)
				o_slaves <= slaves_next;
			if ((tick_1us == 1'b1) && (cnt_dm_en == 1'b1))
				cnt_dm		<= cnt_dm_nxt;
		end
	end
	
	edge_detect_both i_edge_detect_rec_pending(
		.clk_rst     (clk_rst               ), 
		.i_signal    (general_data_writer_inputs.rec_pending           ), 
		.o_pos_edge  (general_data_writer_inputs.rec_pending_posedge   ),
		.o_neg_edge  (general_data_writer_inputs.rec_pending_negedge   ));

	always_comb begin
		dsi_state_nxt = dsi_state;
		rec_enable = 1'b0;
        start_transmit = 1'b0;
		o_acknowledge_start = 1'b0;
		o_finished = 1'b0;
		hw_fail_transceive_fsm = 1'b0;
		mode_next = mode;
		store_empty_packet = 1'b0;
		clear_flag_for_received_packets = 1'b0;

		slaves_next = o_slaves + 4'd1;
		set_slaves = 1'b0;
		cnt_dm_en = 1'b0;
		filter_en = 1'b0;
		cnt_dm_nxt = cnt_dm;
		o_dm_overflow = 1'b0;

		// Combined Actions
		case (dsi_state)
			DSI_IDLE: begin
				o_finished = 1'b1;
				if (i_start == 1'b1) begin
					if (i_mode == MODE_DM) begin
						o_acknowledge_start = 1'b1;
						dsi_state_nxt = DM_SETUP;
						slaves_next = '0;
						set_slaves = 1'b1;
						mode_next = i_mode;
					end
					else begin
                        start_transmit = 1'b1;								// start transmission with the content of CMD_HIGH & CMD_LOW with a length of CMD_LENGTH
						if (acknowledge_start == 1'b1) begin
							dsi_state_nxt = TRANSMIT;
							o_acknowledge_start = 1'b1;
							mode_next = i_mode;
						end
					end
				end
			end
			TRANSMIT: begin
				if (transmit_pending == 1'b0) begin
					if ((i_broad_cast == 1'b1) && (mode == MODE_CRM)) begin
        				if (crm_receive_timeout == 1'b1) begin
    						dsi_state_nxt = DSI_IDLE;
                        end
					end
					else begin
						clear_flag_for_received_packets=1'b1;
						dsi_state_nxt = RECEIVE;
						if (mode == MODE_CRM) begin
							if (crm_receive_timeout == 1'b1) begin
								dsi_state_nxt = DSI_IDLE;
								store_empty_packet = 1'b1;
							end
						end
					end
				end
			end
			RECEIVE: begin
				rec_enable = 1'b1;
				if ((receive_time_out_tick_crm  == 1'b1) || (receive_time_out_tick_pdcm == 1'b1) || (i_stop == 1'b1)) begin
					dsi_state_nxt = DSI_IDLE;
					if (mode == MODE_CRM) begin
						if (received_at_least_one_packet == 1'b0) begin
							store_empty_packet = 1'b1;
						end
					end
				end
			end
			DM_SETUP: begin // TODO: check if it can be removed (or merged with other states)?
                start_transmit = 1'b1;									
				dsi_state_nxt = DM_WAIT_FOR_PULSE;
			end
			DM_WAIT_FOR_PULSE: begin
				cnt_dm_en = 1'b1;
				case (common_config.bit_time)									// set timer
					2'b00, 2'b11: begin
						cnt_dm_nxt = 9'd58;
					end
					2'b01: begin
						cnt_dm_nxt = 9'd116;
					end
					2'b10: begin
						cnt_dm_nxt = 9'd232;
					end
				endcase
				if (o_tx == 1'b0)
					dsi_state_nxt = DM_PULSE;
			end
			DM_PULSE: begin
				cnt_dm_en = 1'b1;
				cnt_dm_nxt = cnt_dm - 9'd1;
				if (o_tx == 1'b1)
					dsi_state_nxt = DM_WAIT_FOR_SLAVE;
			end
			DM_WAIT_FOR_SLAVE: begin
				cnt_dm_en = 1'b1;

				if (cnt_dm != 9'd0) begin
					cnt_dm_nxt = cnt_dm - 9'd1;
				end
				else begin
					dsi_state_nxt = DM_CHECK_SLAVE;
				end
			end
			DM_CHECK_SLAVE: begin
				cnt_dm_nxt = cnt_dm + 9'd1;
				cnt_dm_en = 1'b1;
				filter_en = 1'b1;										// enable filtering for rejecting noise
				if (sensed_new_slave == 1'b1) begin
					dsi_state_nxt = DM_WAIT_FOR_NEXT;
					set_slaves = 1'b1;
				end
				else begin
					if ((chip_in_filtered == 1'b1) && (o_slaves == 4'hf)) begin
						o_dm_overflow = 1'b1;	// set DM Overflow in interrupt register since all possible slaves addressed but still one is responding
                    end
                    case (common_config.bit_time)                                   //DM finished
                        2'b00, 2'b11: begin
                            if (cnt_dm == (9'd44)) 
        						dsi_state_nxt = DSI_IDLE;
                        end
                        2'b01: begin
                            if (cnt_dm == (9'd58)) 
        						dsi_state_nxt = DSI_IDLE;
                        end
                        2'b10: begin
                            if (cnt_dm == (9'd80)) 
        						dsi_state_nxt = DSI_IDLE;
                        end
                    endcase
				end
			end
			DM_WAIT_FOR_NEXT: begin
				cnt_dm_en = 1'b1;
				cnt_dm_nxt = cnt_dm + 9'd1;
                case (common_config.bit_time)                                   // set timer
                    2'b00, 2'b11: begin
        				if (cnt_dm == (9'd67 - TIME_TO_START_TRANSMITTER)) 
        					dsi_state_nxt = DM_SETUP;
                    end
                    2'b01: begin
        				if (cnt_dm == (9'd73 - TIME_TO_START_TRANSMITTER))
        					dsi_state_nxt = DM_SETUP;
                    end
                    2'b10: begin
        				if (cnt_dm == (9'd85 - TIME_TO_START_TRANSMITTER)) 
        					dsi_state_nxt = DM_SETUP;
                    end
                endcase
			end
			default: begin
				dsi_state_nxt = DSI_IDLE;
				hw_fail_transceive_fsm = 1'b1;
			end
		endcase
		if (i_transceiver_enable == 1'b0) begin
			dsi_state_nxt = DSI_IDLE;
		end
	end // Output Block
	
	assign	general_data_writer_inputs.ov = i_ov;
	assign	general_data_writer_inputs.uv = i_uv;
	
    assign  general_data_writer_inputs.time_of_start_transmit = time_of_start_transmit;
    assign  general_data_writer_inputs.time_of_start_receive_after_command = time_of_start_receive - time_of_start_transmit - data_t'(2)*data_t'(get_bit_time_factor(common_config.bit_time));
	
    assign  general_data_writer_inputs.transceiver_enable_negedge = ~i_transceiver_enable & transceiver_enable_previous;
    
	DSI3_channel_registers_PACKET_STAT_if	DSI3_channel_registers_PACKET_STAT_crm();
	DSI3_channel_registers_PACKET_STAT_if	DSI3_channel_registers_PACKET_STAT_pdcm();
	
	packet_stat_multiplexer u_packet_stat_multiplexer (
		.i_mode     (mode                                            ),
		.to_register(DSI3_channel_registers_PACKET_STAT              ),
		.from_crm   (DSI3_channel_registers_PACKET_STAT_crm.master   ),
		.from_pdcm  (DSI3_channel_registers_PACKET_STAT_pdcm.master  ));
	
	dsi3_crm_data_writer i_crm_data_writer (
		.clk_rst                            (clk_rst                          ),
		.time_base                          (time_base                        ),
		.DSI3_channel_registers_PACKET_STAT (DSI3_channel_registers_PACKET_STAT_crm.slave),
		.crm_data_writer                    (crm_data_writer                  ),
		.common_config                      (common_config                    ),
        .general_inputs                     (general_data_writer_inputs.slave ),
		.i_enable                           (mode==MODE_CRM                   ),
		.i_clear_flag_for_received_packets  (clear_flag_for_received_packets  ),
        .i_clear_data_buffer                (i_clear_crm_data_buffer          ),
        .i_clear_and_invalidate_data_buffer (i_clear_and_invalidate_crm_data_buffer),
		.i_store_empty_packet               (store_empty_packet               ),
        .i_received_c0_after_packet         (received_c0_after_packet         ),
        .i_receive_time_out_tick            (receive_time_out_tick_crm        ),
		.o_received_at_least_one_packet     (received_at_least_one_packet     ),
		.o_hw_fail_data_fsm                 (hw_fail_crm_data_fsm             ));
	
	dsi3_pdcm_data_writer i_pdcm_data_writer (
		.clk_rst                           (clk_rst                          ),
		.time_base                         (time_base                        ),
		.DSI3_channel_registers_PACKET_STAT(DSI3_channel_registers_PACKET_STAT_pdcm.slave),
		.DSI3_channel_registers_FRAME_STAT (DSI3_channel_registers_FRAME_STAT),
		.pdcm_data_writer                  (pdcm_data_writer                 ),
        .tdma_reader                       (tdma_reader                      ),
		.common_config                     (common_config                    ),
        .general_inputs                    (general_data_writer_inputs.slave ),
		.i_enable                          (mode==MODE_PDCM                  ),
		.i_clear_flag_for_received_packets (clear_flag_for_received_packets  ),
        .i_clear_data_buffer               (i_clear_pdcm_data_buffer         ),
        .i_clear_and_invalidate_data_buffer(i_clear_and_invalidate_pdcm_data_buffer),
        .i_receive_time_out_tick           (receive_time_out_tick_pdcm       ),
        .i_stop                            (i_stop                           ),
		.o_hw_fail_data_fsm                (hw_fail_pdcm_data_fsm            ),
		.o_received_at_least_one_packet    ());
    
    /*###   ECC_DECCODER - data path to SPI  ##################################*/
    ecc_decoder #(
        .DATA_WIDTH  (DATA_WIDTH),
        .ECC_WIDTH   (ECC_WIDTH)
    ) i_ecc_dec_rx_data (
        .i_correct_n (1'b0),
        .i_data      (general_data_writer_inputs.rx_data.data),
        .i_ecc       (general_data_writer_inputs.rx_data.ecc),
        .o_data      (general_data_writer_inputs.rx_data_corrected),
        .o_ecc_cor   (ecc_error_data.single_error),
        .o_ecc_err   (ecc_error_data.double_error)
    );
    
    `ifdef VCS
        pdcm_buffer_writer_if pdcm_buffer_writer ();
        assign  pdcm_buffer_writer.action   = pdcm_data_writer.action;
        assign  pdcm_buffer_writer.data     = pdcm_data_writer.data;
        
        frame_data_visualizer u_frame_data_visualizer (
            .clk_rst         (clk_rst                   ),
            .pdcm_data_writer(pdcm_buffer_writer.slave )
        );
    `endif

	
	/*###   DSI3 filter   ######################################################*/
	dsi3_chip_filter_for_dm #(
		.debounce_length  (10 )
	) i_dsi3_filter_for_dm (
		.clk_rst          (clk_rst            ), 
		.i_dsi3           (o_rx_filtered      ), 
		.i_tick_1us       (time_base.tick_1us ), 
		.i_enable         (filter_en          ), 
		.o_filtered       (chip_in_filtered   ));
    
endmodule
