/*------------------------------------------------------------------------------
 * File          : dsi3_data_writer.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Feb 28, 2023
 * Description   : Module for writing received data to buffer
 *------------------------------------------------------------------------------*/
module dsi3_crm_data_writer import project_pkg::*; import dsi3_pkg::*; import buffer_if_pkg::*;  (
		clk_reset_if.slave	clk_rst,
		timebase_info_if.slave				time_base,
		DSI3_channel_registers_PACKET_STAT_if.slave	DSI3_channel_registers_PACKET_STAT,
		buffer_writer_if.master				crm_data_writer,
		dsi3_common_config_if.dsi3_block	common_config,
        general_data_writer_inputs_if.slave general_inputs,
		
		input	logic				        i_enable,
		input	logic				        i_clear_flag_for_received_packets,
        input   logic                       i_clear_data_buffer,
        input   logic                       i_clear_and_invalidate_data_buffer,
		input	logic				        i_store_empty_packet,
        input   logic                       i_received_c0_after_packet,
        input   logic                       i_receive_time_out_tick,
		output	logic				        o_received_at_least_one_packet,
		output	logic				        o_hw_fail_data_fsm
	);
	
	/*###   ECC_ENCODER - data path to SPI  ####################################*/
	data_t	dsi_data_writer;
	ecc_t	dsi_data_writer_ecc;
	logic   recalculate_ecc;

	assign crm_data_writer.data.data = dsi_data_writer;
	assign crm_data_writer.data.ecc  = (recalculate_ecc) ? dsi_data_writer_ecc : general_inputs.rx_data.ecc;
	
	ecc_encoder #(
			.DATA_WIDTH  (DATA_WIDTH),
			.ECC_WIDTH   (ECC_WIDTH)
		) i_ecc_enc_dsi3_rec (
			.i_data      (dsi_data_writer),
			.o_ecc       (dsi_data_writer_ecc)
		);
	
	/*#########################################################################*/
	logic	ce_flag, ce_flag_next, ve_flag, ve_flag_next;
	logic	mask_ce_ve_flag_setting, mask_ce_ve_flag_setting_next;
	logic	reset_ce_ve_info_after_writing;
	logic 	symbol_error, symbol_error_next;
	logic	received_at_least_one_packet_next;
	
	logic	reset_package_info;
	logic	reset_package_info_due_to_new_packet;
	assign	reset_package_info_due_to_new_packet = (o_received_at_least_one_packet && general_inputs.received_data && ((general_inputs.symbol_count == 9'd4)?1'b1:1'b0));
	logic	reset_package_info_due_to_new_transmit;
	assign	reset_package_info_due_to_new_transmit = general_inputs.start_transmit;

	assign	reset_package_info = reset_package_info_due_to_new_transmit || reset_package_info_due_to_new_packet;
	logic	symbol_count_error, crc_error;
    logic   receive_pending_at_time_out;
	
	assign	DSI3_channel_registers_PACKET_STAT.SCE_in 			= (reset_package_info == 1'b1) ? 1'b1 : symbol_count_error;
	assign	DSI3_channel_registers_PACKET_STAT.SCE_set 			= reset_package_info | general_inputs.response_finished;
	assign	DSI3_channel_registers_PACKET_STAT.CRC_ERR_in 		= ~reset_package_info;
	assign	DSI3_channel_registers_PACKET_STAT.CRC_ERR_set 		= reset_package_info | crc_error;
	assign	DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_set	= reset_package_info | general_inputs.symbol_error_set;
	assign	DSI3_channel_registers_PACKET_STAT.VDSI_ERR_in 		= ~reset_package_info;
	assign	DSI3_channel_registers_PACKET_STAT.VDSI_ERR_set 	= reset_package_info | (ve_flag & ~mask_ce_ve_flag_setting);
	assign	DSI3_channel_registers_PACKET_STAT.CLK_ERR_in 		= ~reset_package_info;
	assign	DSI3_channel_registers_PACKET_STAT.CLK_ERR_set 		= reset_package_info | (ce_flag & ~mask_ce_ve_flag_setting);
	
    /*###   SE - symbol error   ##################################*/
	always_comb begin // needed for the first 4 Symbols only to save the value until packet info is reset
		symbol_error_next = symbol_error;
		if (general_inputs.rec_pending_posedge == 1'b1) begin
			symbol_error_next = 1'b0;
		end
		else begin
			if (general_inputs.symbol_error_set == 1'b1)
				symbol_error_next = 1'b1;
		end
	end
	
	always_comb begin
		if (reset_package_info_due_to_new_transmit == 1'b1)
			DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_in = 1'b0;
		else begin
			if (reset_package_info_due_to_new_packet == 1'b1) begin
				DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_in = symbol_error || general_inputs.symbol_error_set;
			end
			else begin // symbol error occurs (inputs.symbol_error_set == 1'b1)
				DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_in = 1'b1;
			end
		end
	end
	
    /*###   SYMBOL_COUNT   ##################################*/
	always_comb begin
		if (reset_package_info == 1'b1) begin
			DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_in		= (general_inputs.start_transmit == 1'b1) ? '0 : general_inputs.symbol_count[7:0];
		end
		else begin
			if (general_inputs.symbol_count > 9'd255) begin
				DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_in	= 8'hff;
			end
			else begin
				DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_in	= general_inputs.symbol_count[7:0];
			end
		end
	end
	assign	DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_set	= reset_package_info | general_inputs.response_finished | general_inputs.received_data;
	
    /*###   SCE - symbol count error   ##################################*/
	always_comb begin
		symbol_count_error = 1'b0;
		if (general_inputs.response_finished == 1'b1) begin
  			if (    (general_inputs.symbol_count != 9'd8) ||
                    (general_inputs.symbol_count_overflow == 1'b1))
				symbol_count_error = 1'b1;
		end
	end
	
    /*###   CE | VE   ##################################*/
	always_comb begin
		ce_flag_next = ce_flag | ~time_base.clkref_ok;
		ve_flag_next = ve_flag | general_inputs.ov | general_inputs.uv;
		if ((reset_ce_ve_info_after_writing == 1'b1) || (general_inputs.start_transmit == 1'b1)) begin
			ce_flag_next = ~time_base.clkref_ok;
			ve_flag_next = general_inputs.ov | general_inputs.uv;
		end
	end
	
	always_comb begin
		mask_ce_ve_flag_setting_next = mask_ce_ve_flag_setting;
		if ((general_inputs.received_data == 1'b1) || (general_inputs.start_transmit == 1'b1)) begin // received data used to not store data for less than 4 symbol "responses"
			mask_ce_ve_flag_setting_next = 1'b0;
		end
		if (reset_ce_ve_info_after_writing == 1'b1) begin
			mask_ce_ve_flag_setting_next = 1'b1;
		end
	end
	
    /*###   TE - timing error   ##################################*/
	always_comb begin
		DSI3_channel_registers_PACKET_STAT.TE_in	= ~reset_package_info;
		DSI3_channel_registers_PACKET_STAT.TE_set	= reset_package_info; 
		if (i_enable == 1'b1) begin
			if ((general_inputs.response_finished == 1'b1)) begin
				if ((general_inputs.time_of_start_receive_after_command - DSI3_TIMING_ERROR_CRM_UNCERTAINTY) < (DSI3_TIMING_ERROR_CRM_MIN<<get_bit_time_shift(common_config.bit_time))) begin
					DSI3_channel_registers_PACKET_STAT.TE_set = 1'b1;
					DSI3_channel_registers_PACKET_STAT.TE_in = 1'b1;
				end
				if ((general_inputs.time_of_start_receive_after_command - DSI3_TIMING_ERROR_CRM_UNCERTAINTY) > (DSI3_TIMING_ERROR_CRM_MAX<<get_bit_time_shift(common_config.bit_time))) begin
					if (i_received_c0_after_packet == 1'b0) begin
						DSI3_channel_registers_PACKET_STAT.TE_set = 1'b1;
						DSI3_channel_registers_PACKET_STAT.TE_in = 1'b1;
					end
                end
                if (receive_pending_at_time_out == 1'b1) begin
					DSI3_channel_registers_PACKET_STAT.TE_set = 1'b1;
					DSI3_channel_registers_PACKET_STAT.TE_in = 1'b1;
                end
			end
		end
	end
	
	/*###   CRC calculation   ######################################################*/
	dsi3_crc_t	seed, packet_crc, packet_crc_next;
	logic	initialize_crc, initialize_crc_next;
	logic	check_crc_error;

	dsi3_crc_parallel i_dsi3_crc_parallel (
			.i_seed      (seed ),
			.i_data      (general_inputs.rx_data_corrected     ),
			.o_crc       (packet_crc_next ));
	
	always_comb begin
		if (initialize_crc == 1'b1) begin
			seed = 8'hff;
		end
		else begin
			seed = packet_crc;
		end
	end

	always_comb begin
		crc_error = 1'b0;
		if (check_crc_error == 1'b1) begin
			if (common_config.crc_enable == 1'b1) begin
				if (packet_crc != '0) begin
					crc_error = 1'b1;
				end
				if (general_inputs.symbol_count != 9'd8) begin
					crc_error = 1'b1;
				end
			end
		end
	end
	
	/*###   data FSM   ######################################################*/
	typedef enum logic[2:0] {DATA_IDLE, DATA_WRITE_EMPTY_HEADER, DATA_STORE_DATA, DATA_VALIDATE, DATA_INVALIDATE, DATA_FINISH_PACKET, DATA_CLEAR_BUFFER, DATA_WAIT} data_state_e;
	data_state_e	data_state, data_state_next, data_state_last, data_state_last_next;
	logic	calculate_crc;
	logic	handle_clear_buffer, handle_clear_buffer_next;
	logic	handle_invalidate_buffer, handle_invalidate_buffer_next;
	logic	invalidate_buffer, invalidate_buffer_next;
	
	logic	handle_received_data, handle_received_data_next;
	logic	handle_response_finished, handle_response_finished_next;
	logic	handle_store_empty_packet, handle_store_empty_packet_next;

	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			data_state		<= DATA_IDLE;
			data_state_last	<= DATA_IDLE;
			packet_crc		<= dsi3_crc_t'('hff);
			initialize_crc	<= 1'b1;
			handle_invalidate_buffer	<= 1'b0;
			handle_clear_buffer	<= 1'b0;
			invalidate_buffer <= 1'b0;
			ve_flag			<= 1'b0;
			ce_flag			<= 1'b0;
			mask_ce_ve_flag_setting <= 1'b1;
			handle_response_finished <= 1'b0;
			handle_received_data <= 1'b0;
			o_received_at_least_one_packet <= 1'b0;
			symbol_error	<= 1'b0;
			handle_store_empty_packet <= 1'b0;
            receive_pending_at_time_out <= '0;
		end
		else begin
			data_state		<= data_state_next;
			data_state_last	<= data_state_last_next;
			initialize_crc	<= initialize_crc_next;
			handle_invalidate_buffer	<= handle_invalidate_buffer_next;
			handle_clear_buffer	<= handle_clear_buffer_next;
			invalidate_buffer <= invalidate_buffer_next;
			ce_flag			<= ce_flag_next;
			ve_flag			<= ve_flag_next;
			mask_ce_ve_flag_setting <= mask_ce_ve_flag_setting_next;
			handle_received_data <= handle_received_data_next;
			handle_response_finished <= handle_response_finished_next;
			o_received_at_least_one_packet <= received_at_least_one_packet_next;
			symbol_error	<= symbol_error_next;
			handle_store_empty_packet <= handle_store_empty_packet_next;
			if (calculate_crc == 1'b1)
				packet_crc <= packet_crc_next;
            if (i_receive_time_out_tick == 1'b1) begin
                receive_pending_at_time_out <= general_inputs.rec_pending & ~i_received_c0_after_packet;
            end
            else begin
                if (general_inputs.start_transmit == 1'b1)
                    receive_pending_at_time_out <= 1'b0;
            end
		end
	end

	always_comb begin
		recalculate_ecc = 1'b0;
		data_state_next = data_state;
		dsi_data_writer = general_inputs.rx_data_corrected;
		crm_data_writer.action = IDLE_WRITE;
		calculate_crc = 1'b0;
		check_crc_error = 1'b0;
		invalidate_buffer_next = invalidate_buffer | general_inputs.transceiver_enable_negedge;

		handle_clear_buffer_next = handle_clear_buffer | i_clear_data_buffer;
		handle_invalidate_buffer_next = handle_invalidate_buffer | i_clear_and_invalidate_data_buffer;
		initialize_crc_next = initialize_crc;
		
		reset_ce_ve_info_after_writing = 1'b0;
		data_state_last_next = data_state_last;
		
		handle_received_data_next = handle_received_data | general_inputs.received_data;
		handle_response_finished_next = handle_response_finished | general_inputs.response_finished | general_inputs.rec_pending_negedge;
		
		o_hw_fail_data_fsm = 1'b0;
		
		handle_store_empty_packet_next = handle_store_empty_packet | i_store_empty_packet;
		received_at_least_one_packet_next = o_received_at_least_one_packet & ~i_clear_flag_for_received_packets;

		case (data_state)
			DATA_IDLE: begin
				initialize_crc_next = 1'b1;
				handle_response_finished_next = 1'b0;
				if ((i_clear_data_buffer == 1'b1) || (handle_clear_buffer)) begin
					data_state_next = DATA_CLEAR_BUFFER;
					data_state_last_next = DATA_IDLE;
				end
				else begin
                    if (i_enable == 1'b1) begin
						if (o_received_at_least_one_packet == 1'b0) begin
        					if (((general_inputs.received_data == 1'b1) || (handle_received_data == 1'b1))) begin // P52143-488
        						handle_received_data_next = 1'b0;
        						handle_response_finished_next = general_inputs.response_finished;
        						data_state_next = DATA_WRITE_EMPTY_HEADER;
        						data_state_last_next = DATA_STORE_DATA;
        						handle_store_empty_packet_next = 1'b0;
        					end
        					else begin
        						if (handle_store_empty_packet == 1'b1) begin
    								handle_store_empty_packet_next = 1'b0;
    								data_state_next = DATA_WRITE_EMPTY_HEADER;
    								data_state_last_next = DATA_VALIDATE;
    							end
    						end
                        end
                        else begin
                            handle_response_finished_next = 1'b0;
                            handle_received_data_next = 1'b0;
                            handle_store_empty_packet_next = i_store_empty_packet; 
                        end
                    end
                    else begin
                        handle_received_data_next = 1'b0;
                        handle_store_empty_packet_next = 1'b0; 
                        handle_response_finished_next = 1'b0;
                    end
				end
			end
			DATA_WRITE_EMPTY_HEADER: begin
				recalculate_ecc = 1'b1;
				crm_data_writer.action = BUFFER_WRITE;
				dsi_data_writer = DSI3_channel_registers_PACKET_STAT.value;
				if (crm_data_writer.ready == 1'b1) begin
					data_state_next = data_state_last;
					calculate_crc = 1'b1;
				end
			end
			DATA_WAIT: begin
				initialize_crc_next = 1'b0;
				if ((i_clear_data_buffer == 1'b1) || (handle_clear_buffer)) begin
					data_state_next = DATA_CLEAR_BUFFER;
					data_state_last_next = DATA_WAIT;
				end
				else begin
					if (handle_response_finished == 1'b1) begin
						data_state_next = DATA_FINISH_PACKET;
						check_crc_error = 1'b1;
					end
					else begin
						if ((general_inputs.received_data == 1'b1) || (handle_received_data == 1'b1)) begin
							if (handle_received_data == 1'b1) begin
								handle_received_data_next = general_inputs.received_data;
							end
							else begin
								handle_received_data_next = 1'b0;
							end
							data_state_next = DATA_STORE_DATA;
							calculate_crc = 1'b1;
						end
						else begin
							if (general_inputs.response_finished == 1'b1) begin // handle_response_finished is 1'b0 first if-clause
								data_state_next = DATA_FINISH_PACKET;
								check_crc_error = 1'b1;
							end
						end
					end
				end
			end
			DATA_STORE_DATA: begin
				if (general_inputs.symbol_count <= 9'd8) begin
					crm_data_writer.action = BUFFER_WRITE;
					if (crm_data_writer.ready == 1'b1) begin
						data_state_next = DATA_WAIT;
					end
				end
				else begin
					data_state_next = DATA_WAIT;
				end
			end
			DATA_FINISH_PACKET: begin
				if (general_inputs.symbol_count >= 9'd4 ) begin
					recalculate_ecc = 1'b1;
					crm_data_writer.action = BUFFER_WRITE_FIRST;
					dsi_data_writer = DSI3_channel_registers_PACKET_STAT.value;
					if (crm_data_writer.ready == 1'b1) begin
						received_at_least_one_packet_next = 1'b1;
						data_state_next = DATA_VALIDATE;
						handle_response_finished_next = 1'b0;
						reset_ce_ve_info_after_writing = 1'b1;
						handle_store_empty_packet_next = 1'b0;
					end
				end
				else begin
					data_state_next = DATA_INVALIDATE;
				end
			end
			DATA_VALIDATE: begin
				crm_data_writer.action = BUFFER_VALIDATE;
				if (crm_data_writer.ready == 1'b1) begin
					data_state_next = DATA_IDLE;
				end
				handle_response_finished_next = 1'b0;
			end
			DATA_INVALIDATE: begin
				crm_data_writer.action = BUFFER_INVALIDATE;
				if (crm_data_writer.ready == 1'b1) begin
					data_state_next = DATA_IDLE;
				end
				handle_response_finished_next = 1'b0;
				invalidate_buffer_next = 1'b0;
			end
			DATA_CLEAR_BUFFER: begin
				if(handle_invalidate_buffer == 1'b1)
					crm_data_writer.action = BUFFER_CLEAR_AND_INVALIDATE_NEXT;
				else 
					crm_data_writer.action = BUFFER_CLEAR;
				if (crm_data_writer.ready == 1'b1) begin
					handle_clear_buffer_next = 1'b0;
					handle_invalidate_buffer_next = 1'b0;
					data_state_next = data_state_last;
				end
			end
			default: begin
				data_state_last_next = DATA_INVALIDATE;
				data_state_next = DATA_CLEAR_BUFFER;	
				o_hw_fail_data_fsm = 1'b1;
			end
		endcase
		if ((invalidate_buffer | general_inputs.transceiver_enable_negedge) == 1'b1) begin
			data_state_next = DATA_INVALIDATE;
		end
	end
	
endmodule