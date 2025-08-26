/**
 * Module: command_control
 *
 * Controlling command flow
 */
module command_control import project_pkg::*; import buffer_if_pkg::*;(
		clk_reset_if.slave		clk_rst,
		elip_full_if.master		elip_write_register,
		buffer_reader_if.master	command_reader,
		buffer_writer_if.master dsi_command_writer[DSI_CHANNELS-1:0],
		
		command_control_to_dsi3_if.master	to_dsi3,

		ecc_error_if.master		ecc_error,
		
		input	dsi_logic_t		i_clear_dsi3_command_queue,
		output	logic			o_hw_fail,
		output	logic			o_clear_command_queue,
        output  logic           o_set_command_ignored
	);
	
	import spi_implementation_pkg::*;
	
	typedef enum logic [3:0] {
		IDLE = 4'd0,
		DECODE,
		WRITE_REGISTER_0,
		WRITE_REGISTER_1,
		DSI_WRITE_BUFFER,
		DSI_VALIDATE_BUFFER,
		DSI_INVALIDATE_BUFFERS,
		DSI_READ_NEXT_COMMAND_WORD,
		CLEAR_DSI_COMMAND_QUEUE,
		CLEAR_DSI_DATA_BUFFER,
		DELETE_DSI_COMMAND_QUEUE
	} command_control_state_e;

	command_control_state_e state, state_next;
	spi_command_t command, command_next;
	ecc_t command_ecc, command_ecc_next;

	// for Register Write
	logic[11:0] address, address_next;

	// for DSI commands
	typedef logic[3:0]	command_counter_t;
	command_counter_t	command_counter, command_counter_next;
	dsi_logic_t			channels, channels_next;
	dsi_logic_t			command_written, command_written_next;

	buffer_writer_action_e	command_writer_action[DSI_CHANNELS-1:0];
	dsi_logic_t	command_writer_ready;

	dsi_logic_t	cleared_dsi3_command_buffer, clear_dsi3_command_buffer;
	
	dsi_logic_t	register_sync, register_sync_next;
	
	logic	handle_ecc_error, handle_ecc_error_next;
	logic	clear_command;

	/*###   ECC_DECODER   ######################################################*/
	spi_command_t command_ecc_corrected;
    logic   command_ecc_corr, command_ecc_fail;

	ecc_decoder #(
			.DATA_WIDTH  (DATA_WIDTH),
			.ECC_WIDTH   (ECC_WIDTH)
		) i_ecc_dec_spi (
			.i_correct_n (1'b0),
			.i_data      (command),
			.i_ecc       (command_ecc),
			.o_data      (command_ecc_corrected),
			.o_ecc_cor   (command_ecc_corr),
			.o_ecc_err   (command_ecc_fail)
		);
    
	/*###   ECC register   ######################################################*/
    `include "ecc_register_inc.sv"
    `ecc_register(channels, (DSI_CHANNELS), '0)
    `ecc_register(command_counter, 4, '0)
    
    assign  ecc_error.single_error = command_ecc_corr | channels_ecc_corr | command_counter_ecc_corr;
    assign  ecc_error.double_error = command_ecc_fail | channels_ecc_fail | command_counter_ecc_fail;
    
	/*###   interface array manipulation   ######################################################*/
	generate
		genvar i;
		for (i=0; i<DSI_CHANNELS; i++) begin : generate_dsi_command_writer_interface_connections
			assign dsi_command_writer[i].data.data = command_ecc_corrected;
			assign dsi_command_writer[i].data.ecc = command_ecc;
			assign dsi_command_writer[i].action = command_writer_action[i];
			assign command_writer_ready[i] = dsi_command_writer[i].ready;
		end
	endgenerate

	/*###   command buffer clearing   ######################################################*/
	control_command_buffer_clearing i_control_command_buffer_clearing (
			.clk_rst                   (clk_rst                    ),
			.i_dsi3_enabled            (to_dsi3.dsi3_enabled       ),
			.i_cleared_command_buffer  (cleared_dsi3_command_buffer),
			.i_clear_command_buffer    (i_clear_dsi3_command_queue ),
			.o_clear_command_buffer    (clear_dsi3_command_buffer  ));

	/*###   FFs   ######################################################*/
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			state <= IDLE;
			address <= '0;
			command <= '0;
			command_ecc <= ECC_FOR_DATA_0;
			command_written <= '0;
			register_sync <= '0;
			handle_ecc_error <= 1'b0;
		end
		else begin
			state <= state_next;
			address <= address_next;
			command_written <= command_written_next;
			register_sync <= register_sync_next;
			handle_ecc_error <= handle_ecc_error_next;
			if ((command_reader.ready == 1'b1) || (clear_command == 1'b1)) begin
				command <= command_next;
				command_ecc <= command_ecc_next;
			end
		end
	end
	
	always_comb begin
		if (clear_command == 1'b1) begin
			command_next = '0;
			command_ecc_next = ECC_FOR_DATA_0;
		end
		else begin
			command_next = spi_command_t'(command_reader.data.data);
			command_ecc_next = command_reader.data.ecc;
		end
	end

	assign	command_reader.step = '0;

	/*###   FSM - common state actions   ######################################################*/
	`define clear_command_queue(_next_state_) to_dsi3.stop_transmission = channels; \
		for (int i=0; i<DSI_CHANNELS; i++) begin \
			if (channels[i] == 1'b1) begin \
				if (~command_written[i] == 1'b1) \
					command_writer_action[i] = BUFFER_CLEAR; \
				if (command_writer_ready[i] == 1'b1) begin \
					command_written_next[i] = 1'b1; \
					cleared_dsi3_command_buffer[i] = 1'b1; \
				end \
			end \
		end \
		if (command_written == channels) begin \
			state_next = _next_state_; \
			command_written_next = '0; \
		end 
	
	`define hardware_fail state_next = DELETE_DSI_COMMAND_QUEUE; \
		command_written_next = '0; \
		channels_next = '1; \
		o_hw_fail = 1'b1; \
		o_clear_command_queue = 1'b1;
		
	`define handle_ecc(_next_state_) handle_ecc_error_next = 1'b0; \
		state_next = _next_state_; \
		command_written_next = '0; \
		channels_next = '1; \
		clear_command = 1'b1; \
		o_clear_command_queue = 1'b1;
		
	
	`define if_queue_is_not_empty_begin if (command_reader.empty == 1'b1) begin \
		state_next = DSI_INVALIDATE_BUFFERS; \
		command_written_next = '0; \
		channels_next = '1; \
		o_clear_command_queue = 1'b1; \
		o_hw_fail = 1'b1; \
		end \
		else begin
		
	/*###   FSM   ######################################################*/
	logic	ecc_error_present;
	assign	ecc_error_present = (ecc_error.double_error | handle_ecc_error);
    
	always_comb begin
		address_next = address;
		command_reader.action = IDLE_READ;
		channels_next = channels;
		command_counter_next = command_counter;
		command_written_next = command_written;

		for (int i=0; i<DSI_CHANNELS; i++)
			command_writer_action[i] = IDLE_WRITE;

		elip_write_register.rd = 1'b0;
		elip_write_register.wr = 1'b0;
		elip_write_register.data_write.data = command_ecc_corrected;
		elip_write_register.data_write.ecc = command_ecc;
		elip_write_register.addr = elip_addr_t'(address);

		state_next = state;

		to_dsi3.stop_transmission = '0;
		to_dsi3.clear_crm_data_buffer = '0;
		to_dsi3.clear_pdcm_data_buffer = '0;
        to_dsi3.set_command_error = '0;
        to_dsi3.set_sync_error = '0;
		to_dsi3.register_sync = '0;

		cleared_dsi3_command_buffer = '0;
		register_sync_next = '0;
		
		handle_ecc_error_next = handle_ecc_error | ecc_error.double_error;
		o_hw_fail = 1'b0;
		clear_command = 1'b0;
		o_clear_command_queue = 1'b0;
        o_set_command_ignored = 1'b0;

		case (state)
			IDLE: begin
				if (ecc_error_present == 1'b1) begin
					`handle_ecc(IDLE)
				end
				else begin
					command_counter_next = '0;
					command_written_next = '0;
					channels_next = '0;
					if (clear_dsi3_command_buffer != '0) begin // clear before evaluating next commands
						channels_next = clear_dsi3_command_buffer;
						state_next = CLEAR_DSI_COMMAND_QUEUE;
					end
					else begin
						if (command_reader.empty == 1'b0) begin
							command_reader.action = BUFFER_READ;
							if (command_reader.ready == 1'b1) begin
								state_next = DECODE;
							end
						end
					end
				end
			end

			DECODE: begin
				if (ecc_error_present == 1'b1) begin
					`handle_ecc(IDLE)
				end
				else begin
					command_counter_next = command_counter_t'(get_command_length(command_ecc_corrected) - 1);
					case (command_ecc_corrected.command)
						REG_WRITE: begin
							address_next = command_ecc_corrected.data;
							state_next = WRITE_REGISTER_0;
						end
						DSI_CRM, DSI_PDCM, DSI_WAIT, DSI_START_DISCOVERY, DSI_UPLOAD_TDMA, DSI_ILOAD: begin
                            if (command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] == '0)
                                o_set_command_ignored = 1'b1;
							channels_next = command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] & to_dsi3.dsi3_enabled;
                            to_dsi3.set_command_error = (command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] & ~to_dsi3.dsi3_enabled);
							state_next = DSI_WRITE_BUFFER;
						end
						CLEAR_COMMAND_QUEUE: begin
                            if (command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] == '0)
                                o_set_command_ignored = 1'b1;
							channels_next = command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT];
							state_next = CLEAR_DSI_COMMAND_QUEUE;
                        end
						CLEAR_DSI_BUFFERS: begin
                            if (command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] == '0)
                                o_set_command_ignored = 1'b1;
							channels_next = command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT];
							state_next = CLEAR_DSI_DATA_BUFFER;
						end
						SYNC: begin
                            if (command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] == '0)
                                o_set_command_ignored = 1'b1;
							channels_next = command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] & to_dsi3.dsi3_enabled;
                            to_dsi3.set_command_error = (command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] & ~to_dsi3.dsi3_enabled);
                            to_dsi3.set_sync_error = (command_ecc_corrected.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] & ~to_dsi3.dsi3_enabled);
							state_next = DSI_WRITE_BUFFER;
							register_sync_next = channels_next;
						end
						default: begin
							`hardware_fail
						end
					endcase
				end
			end

			WRITE_REGISTER_0 : begin
				`if_queue_is_not_empty_begin
					command_reader.action = BUFFER_READ;
					if (command_reader.ready == 1'b1) begin
						state_next = WRITE_REGISTER_1;
					end
				end
			end
			WRITE_REGISTER_1 : begin
				if (ecc_error_present == 1'b1) begin
					`handle_ecc(IDLE)
				end
				else begin
					if ((address >= 12'h020) && (address < 12'h400)) begin
						elip_write_register.wr = 1'b1;
						if (elip_write_register.ready == 1'b1) begin
							state_next = IDLE;
						end
					end
					else begin
						state_next = IDLE;
					end
				end
			end

			DSI_WRITE_BUFFER : begin
				if (ecc_error_present == 1'b1) begin
					`handle_ecc(DSI_INVALIDATE_BUFFERS)
				end
				else begin
					register_sync_next = register_sync;
					for (int i=0; i<DSI_CHANNELS; i++) begin
						if (channels[i] == 1'b1) begin
							if (~command_written[i] == 1'b1)
								command_writer_action[i] = BUFFER_WRITE;
							if (command_writer_ready[i] == 1'b1) begin
								if (register_sync[i] == 1'b1) begin
									to_dsi3.register_sync[i] = 1'b1;
								end
								command_written_next[i] = 1'b1;
							end
						end
					end
					if (command_written == channels) begin
						command_written_next = '0;
						if (command_counter == command_counter_t'(0)) begin
							state_next = DSI_VALIDATE_BUFFER;
						end
						else begin
							command_counter_next = command_counter - command_counter_t'(1);
							state_next = DSI_READ_NEXT_COMMAND_WORD;
						end
					end
				end
			end

			DSI_VALIDATE_BUFFER: begin
                if (ecc_error_present == 1'b1) begin
                    `handle_ecc(DSI_INVALIDATE_BUFFERS)
                end
                else begin
    				for (int i=0; i<DSI_CHANNELS; i++) begin
    					if (channels[i] == 1'b1) begin
    						if (~command_written[i] == 1'b1)
    							command_writer_action[i] = (to_dsi3.dsi3_enabled[i] == 1'b1) ? BUFFER_VALIDATE : BUFFER_INVALIDATE;
    						if (command_writer_ready[i] == 1'b1) begin
    							command_written_next[i] = 1'b1;
    						end
    					end
    				end
    				if (command_written == channels) begin
    					state_next = IDLE;
                    end
                end
			end
			
			DSI_INVALIDATE_BUFFERS: begin
                if (ecc_error_present == 1'b1) begin
                    `handle_ecc(DSI_INVALIDATE_BUFFERS)
                end
                else begin
    				for (int i=0; i<DSI_CHANNELS; i++) begin
    					if (channels[i] == 1'b1) begin
    						if (~command_written[i] == 1'b1)
    							command_writer_action[i] = BUFFER_INVALIDATE;
    						if (command_writer_ready[i] == 1'b1) begin
    							command_written_next[i] = 1'b1;
    						end
    					end
    				end
    				if (command_written == channels) begin
    					state_next = IDLE;
                    end
                end
			end

			DSI_READ_NEXT_COMMAND_WORD: begin
				`if_queue_is_not_empty_begin
					command_reader.action = BUFFER_READ;
					if (command_reader.ready == 1'b1) begin
						state_next = DSI_WRITE_BUFFER;
					end
				end
			end

			CLEAR_DSI_COMMAND_QUEUE: begin
				`clear_command_queue(IDLE)
			end
			
			DELETE_DSI_COMMAND_QUEUE: begin
				`clear_command_queue(DSI_INVALIDATE_BUFFERS)
			end

			CLEAR_DSI_DATA_BUFFER: begin
                if (command_ecc_corrected.data[BIT_CLEAR_DSI_BUFFERS_CR] == 1'b1)
				    to_dsi3.clear_crm_data_buffer = channels;
                if (command_ecc_corrected.data[BIT_CLEAR_DSI_BUFFERS_PD] == 1'b1)
                    to_dsi3.clear_pdcm_data_buffer = channels;
				state_next = IDLE;
			end

			default : begin
				`hardware_fail
			end
		endcase
	end
		
endmodule


