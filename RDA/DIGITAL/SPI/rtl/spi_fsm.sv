//------------------------------------------------------------------------------
// Copyright (c) 2023 Elmos SE
// Author        : jvoi
// Creation date : 2023-03-03
// Description   : SPI state machine controlling command writing and reading of data
//------------------------------------------------------------------------------*/
module spi_fsm import project_pkg::*; import buffer_if_pkg::*; import spi_implementation_pkg::*; (
		clk_reset_if.slave      clk_rst,
		elip_full_if.master     elip_spi_read,
		buffer_writer_if.master command_writer,
		buffer_reader_if.master dsi3_pdcm_data_reader,
		buffer_reader_if.master dsi3_crm_data_reader,
		spi_status_if.spi       spi_status,
		ecc_error_if.master     ecc_error_rx_data,
		ecc_error_if.master     data_reader_ecc_error,
		
		input	logic           i_clear_command_queue,
		input	logic			i_write_not_allowed,
		input	logic			i_fifo_full,
		input	data_ecc_t		i_rx_data,
		input	logic			i_received_word,
		input	logic			i_tx_data_available,
        input   logic           i_some_tx_data_in_fifo,
        input   dsi_logic_t     i_no_tdma_scheme_defined,
        input   logic           i_reset_command_received,
        input   logic           i_alignment_error,
        input   data_t          i_tdma_frame_word_count[DSI_CHANNELS-1:0],
        input   logic           i_ram_initialized,
		
		output	dsi_select_t    o_dsi3_pdcm_data_read_channel_select,
		output	dsi_select_t    o_dsi3_crm_data_read_channel_select,
		output	data_ecc_t		o_fifo_data,
		output	logic			o_set_fifo_data,
		output	logic			o_clear_fifo,
		output	logic			o_hardware_fail,
		output	logic			o_command_in_pending,
		output	logic			o_crc_error,
        output  logic           o_set_command_ignored,
		output	logic			o_command_incomplete,
        output  logic           o_expect_command_nibble,
        output  spi_command_e   o_command_nibble
	);
    
	logic	command_in_pending_next;
	logic	handle_received_word, handle_received_word_next;
	logic	get_writer_access_fsm, get_writer_access_clearing, granted_access_fsm, granted_access_clearing;
	
	data_t	crc_in, crc_in_next;
	logic	reset_crc;
	logic	word_based_crc_of_input_correct;
	
	packet_reader_if crm_packet_reader ();
	packet_reader_if pdcm_frame_reader ();
    
    logic   hw_fail_crm_packet_reader;
	
	/*###   ECC decoder RX data   ######################################################*/
    data_t  rx_data_corrected;
    ecc_decoder #(.DATA_WIDTH(DATA_WIDTH), .ECC_WIDTH(ECC_WIDTH)) i_ecc_decoder_rx_datat (
        .i_correct_n(1'b0),
        .i_data     (i_rx_data.data     ),
        .i_ecc      (i_rx_data.ecc      ),
        .o_data     (rx_data_corrected            ),
        .o_ecc_cor  (ecc_error_rx_data.single_error  ),
        .o_ecc_err  (ecc_error_rx_data.double_error  )
    );
    
	/*###   CRC    ######################################################*/
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (!clk_rst.rstn) begin
			crc_in	<= CRC_RESET;
		end
		else begin
			if ((i_received_word == 1'b1) || (reset_crc == 1'b1) || (i_reset_command_received == 1'b1))
				crc_in	<= crc_in_next;
		end
	end
	
	always_comb begin
		if ((reset_crc == 1'b1) || (i_reset_command_received == 1'b1)) begin
			crc_in_next = CRC_RESET;
        end
		else 
			crc_in_next = crc_ccitt_16_word(crc_in, rx_data_corrected);
	end
	assign	word_based_crc_of_input_correct = (crc_in == '0) ? 1'b1 : 1'b0;
    
	/*###   command FSM   ######################################################*/
	buffer_writer_access_arbiter i_buffer_writer_access_arbiter (
		.clk_rst                (clk_rst                   ),
		.i_get_access_fsm       (get_writer_access_fsm     ),
		.i_get_access_clearing  (get_writer_access_clearing),
		.o_grant_access_fsm     (granted_access_fsm        ),
		.o_grant_access_clearing(granted_access_clearing   ));
	
	spi_command_t command;
	spi_command_state_e state, state_next;
	elip_addr_t	address, address_next;
	logic	store_address;
	
	typedef	logic[1:0]	current_channel_t; //TODO: make dependent to DSI_CHANNELS -> DSI_CHANNELS=2^N -> N=?
	current_channel_t	current_channel, current_channel_next;
	
	packet_read_command_info_t	packet_read_command_info, packet_read_command_info_next;
	word_count_t	current_packet_header_word_count, current_packet_header_word_count_next;
	word_count_t	packet_word_counter, packet_word_counter_next;
	
	typedef logic[2:0] word_counter_t;
	word_counter_t word_counter, word_counter_next; //TODO: use packet_word_counter for that (merge)
	
	logic	store_packet_info;
	logic	forbid_writing_to_buffer_and_invalidate_at_the_end, forbid_writing_to_buffer_and_invalidate_at_the_end_next;
	
	logic	was_queueing_command, was_queueing_command_next;
	
	logic	handle_clear_command_queue, handle_clear_command_queue_next;
    logic   invalidate_command_queue, invalidate_command_queue_next;
    
    logic   expect_command_nibble_next;
    spi_command_e   command_nibble_next;
	
	assign  command = spi_command_t'(rx_data_corrected);
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			state <= NO_COMMAND;
			packet_read_command_info <= '{'0};
			packet_word_counter <= '0;
			
			word_counter <= '0;
			o_command_in_pending <= 1'b0;
			was_queueing_command <= 1'b0;
			address <= '0;
			current_channel <= '0;
			current_packet_header_word_count <= '0;
			forbid_writing_to_buffer_and_invalidate_at_the_end <= 1'b0;
			handle_received_word <= 1'b0;
			handle_clear_command_queue <= 1'b0;
            invalidate_command_queue <= 1'b0;
            o_expect_command_nibble <= 1'b0;
            o_command_nibble <= IC_STATUS;
		end
		else begin
			state <= state_next;
			packet_word_counter <= packet_word_counter_next;
			
			word_counter <= word_counter_next;
			o_command_in_pending <= command_in_pending_next;
			was_queueing_command <= was_queueing_command_next;
			if (store_address == 1'b1)
				address <= address_next;
			if (store_packet_info == 1'b1) begin
				packet_read_command_info <= packet_read_command_info_next;
			end
			current_packet_header_word_count <= current_packet_header_word_count_next;
			current_channel <= current_channel_next;
			forbid_writing_to_buffer_and_invalidate_at_the_end <= forbid_writing_to_buffer_and_invalidate_at_the_end_next;
			handle_received_word <= handle_received_word_next;
			handle_clear_command_queue <= handle_clear_command_queue_next;
            invalidate_command_queue <= invalidate_command_queue_next;
            o_expect_command_nibble <= expect_command_nibble_next;
            o_command_nibble <= command_nibble_next;
		end
	end
	
	assign  command_writer.data.data = i_rx_data.data;
	assign  command_writer.data.ecc = i_rx_data.ecc;
	assign	o_dsi3_pdcm_data_read_channel_select =  current_channel[1:0];
	assign	o_dsi3_crm_data_read_channel_select =  current_channel[1:0];
	
	
	/*###   ECC  #######################################*/
	ecc_error_if	pdcm_data_ecc_error();
	ecc_error_if	crm_data_ecc_error();
	
	always_comb begin
		data_reader_ecc_error.single_error = '0;
		data_reader_ecc_error.double_error = '0;
		if ((crm_data_ecc_error.single_error == 1'b1) || (pdcm_data_ecc_error.single_error == 1'b1))
			data_reader_ecc_error.single_error[current_channel] = 1'b1;
		if ((crm_data_ecc_error.double_error == 1'b1) || (pdcm_data_ecc_error.double_error == 1'b1))
			data_reader_ecc_error.double_error[current_channel] = 1'b1;
	end	
	
	logic	clear_command_queue;
	assign	clear_command_queue = i_clear_command_queue | handle_clear_command_queue;
    
    logic   invalidate_command_queue_signals;
    assign  invalidate_command_queue_signals = i_reset_command_received  | i_alignment_error | ecc_error_rx_data.double_error;
    
	`define if_writing_allowed_begin if (i_write_not_allowed == 1'b1) begin \
					forbid_writing_to_buffer_and_invalidate_at_the_end_next = 1'b1; \
					state_next = NO_COMMAND; \
                    o_set_command_ignored = 1'b1; \
				end \
				else begin
	
	// forbid_writing_to_buffer_and_invalidate_at_the_end --> no writing allowed
	
	always_comb begin
		state_next = state;
		word_counter_next = word_counter;
		command_in_pending_next = o_command_in_pending;
		command_writer.action = IDLE_WRITE;
		
		packet_word_counter_next = packet_word_counter;
		
		was_queueing_command_next = was_queueing_command;
		store_address = 1'b0;
		store_packet_info = 1'b0;
		address_next = address;
		current_channel_next = current_channel;
        elip_spi_read.rd = 1'b0;
		o_fifo_data.data = '0;
		o_fifo_data.ecc = ECC_FOR_DATA_0;
		o_set_fifo_data = 1'b0;
		
		current_packet_header_word_count_next = current_packet_header_word_count;
		packet_read_command_info_next = packet_read_command_info;
		
		o_crc_error = 1'b0;
		o_command_incomplete = 1'b0;
		
		
		forbid_writing_to_buffer_and_invalidate_at_the_end_next = ~i_reset_command_received & (forbid_writing_to_buffer_and_invalidate_at_the_end | i_clear_command_queue | i_alignment_error | ecc_error_rx_data.double_error);
		handle_received_word_next = handle_received_word | i_received_word;
		
		handle_clear_command_queue_next = clear_command_queue;
        invalidate_command_queue_next = invalidate_command_queue | invalidate_command_queue_signals;
		o_hardware_fail = hw_fail_crm_packet_reader;
		
		get_writer_access_clearing = 1'b0;
		get_writer_access_fsm = 1'b0;
		
		reset_crc = 1'b0;
		
		crm_packet_reader.get_data = 1'b0;
		crm_packet_reader.abort = 1'b0;
		
		pdcm_frame_reader.get_data = 1'b0;
		pdcm_frame_reader.abort = 1'b0;
        
        command_nibble_next = o_command_nibble;
        expect_command_nibble_next = o_expect_command_nibble;
        o_clear_fifo = 1'b0;
        o_set_command_ignored = 1'b0;
		
		if ((handle_clear_command_queue == 1'b1) || (invalidate_command_queue == 1'b1) || (ecc_error_rx_data.double_error == 1'b1)) begin
            expect_command_nibble_next = 1'b0;
			get_writer_access_clearing = 1'b1;
            o_clear_fifo = 1'b1;
			if (granted_access_clearing == 1'b1) begin
                if (invalidate_command_queue == 1'b1) begin
                    command_writer.action = BUFFER_INVALIDATE;
    				if (command_writer.ready == 1'b1) begin
                        invalidate_command_queue_next = invalidate_command_queue_signals;
    				end
                end
                else begin
    				command_writer.action = BUFFER_CLEAR;
    				if (command_writer.ready == 1'b1) begin
    					handle_clear_command_queue_next = i_reset_command_received | i_clear_command_queue;
    					get_writer_access_clearing = 1'b0;
    				end
                end
			end
        end
        else begin
    		case (state)
    			NO_COMMAND: begin
    				if (forbid_writing_to_buffer_and_invalidate_at_the_end == 1'b0) begin
    					if ((i_received_word == 1'b1) || (handle_received_word == 1'b1)) begin
    						handle_received_word_next = 1'b0;
    						case (command.command)
                                IC_STATUS: begin
                                    // nothing to be done here
                                end
    							CRC_OUT: begin // MOSI CRC will be shiftet in
    								state_next = CHECK_MOSI_CRC;
    								command_in_pending_next = 1'b1;
                                end
                                RESET: begin
                                    // nothing to be done here and wait for next command
                                end
    							// multi word commands
    							REG_WRITE, DSI_CRM, DSI_WAIT, DSI_UPLOAD_TDMA: begin
    								`if_writing_allowed_begin
    									word_counter_next = word_counter_t'(get_command_length(command) - 1);
    									state_next = WRITE_COMMAND;
    									command_in_pending_next = 1'b1;
    									was_queueing_command_next = 1'b1;
    									get_writer_access_fsm = 1'b1;
    								end
    							end
    							// single word commands
    							SYNC, CLEAR_DSI_BUFFERS, CLEAR_COMMAND_QUEUE, DSI_PDCM, DSI_START_DISCOVERY, DSI_ILOAD: begin
                                    `if_writing_allowed_begin
    									state_next = WRITE_COMMAND;
    									was_queueing_command_next = 1'b1;
    									get_writer_access_fsm = 1'b1;
    								end
    							end
    							REG_READ: begin
    								state_next = READ_REGISTER;
    								command_in_pending_next = 1'b1;
    								store_address = 1'b1;
    								address_next = {4'h0,command.data};
                                    expect_command_nibble_next = 1'b1;
                                    command_nibble_next = command.command;
    							end
    							DSI_READ_PDCM_DATA: begin
    								`if_writing_allowed_begin
    									command_in_pending_next = 1'b1;
    									store_packet_info = 1'b1;
    									packet_read_command_info_next.channels = command.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT];
    									packet_word_counter_next = '0;
    									current_channel_next = '0;
    									state_next = READ_PDCM_CHANNEL;
                                        expect_command_nibble_next = 1'b1;
                                        command_nibble_next = command.command;
                                        if(command.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] == '0)
                                            o_set_command_ignored = 1'b1;
    								end
    							end
    							DSI_READ_CRM_DATA: begin
    								`if_writing_allowed_begin
    									command_in_pending_next = 1'b1;
    									store_packet_info = 1'b1;
    									packet_read_command_info_next.channels = command.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT];
    									packet_word_counter_next = '0;
    									current_channel_next = '0;
    									state_next = READ_CRM_CHANNEL;
                                        expect_command_nibble_next = 1'b1;
                                        command_nibble_next = command.command;
                                        if(command.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT] == '0)
                                            o_set_command_ignored = 1'b1;
    								end
    							end
    							default : begin
    								forbid_writing_to_buffer_and_invalidate_at_the_end_next = 1'b1;
    							end
    						endcase
    					end
                    end
                    else begin
                        if ((i_received_word == 1'b1) || (handle_received_word == 1'b1)) begin
                            handle_received_word_next = 1'b0;
                            if ((rx_data_corrected != '1) && (i_reset_command_received != 1'b1))
                                o_set_command_ignored = 1'b1;
                        end
                    end
    			end
    			
    			/*###   MOSI CRC   ######################################################*/
    			CHECK_MOSI_CRC: begin
                    if (forbid_writing_to_buffer_and_invalidate_at_the_end == 1'b1) begin
    					state_next = NO_COMMAND;
    					o_crc_error = 1'b1;
                    end
                    else begin
        				if ((handle_received_word == 1'b1)) begin
        					get_writer_access_fsm = 1'b1;
        					if (granted_access_fsm == 1'b1) begin
        						if (word_based_crc_of_input_correct == 1'b1) begin
        							command_writer.action = BUFFER_VALIDATE;
        						end
        						else begin
        							command_writer.action = BUFFER_INVALIDATE;
        							o_crc_error = 1'b1;
        						end
        						if (command_writer.ready == 1'b1) begin
        							get_writer_access_fsm = 1'b0;
        							state_next = NO_COMMAND;
        							was_queueing_command_next = 1'b0;
        							command_in_pending_next = 1'b0;
        							handle_received_word_next = 1'b0;
        							reset_crc = 1'b1;
        						end
        					end
        					command_in_pending_next = 1'b0;
                        end
    				end
    			end
    			
    			/*###   Queue commands   ######################################################*/
    			WRITE_COMMAND: begin
                    if (ecc_error_rx_data.double_error == 1'b1) begin
                        state_next = NO_COMMAND;
                        command_in_pending_next = 1'b0;
                        forbid_writing_to_buffer_and_invalidate_at_the_end_next = 1'b1;
                    end
                    else begin
        				get_writer_access_fsm = 1'b1;
        				if (granted_access_fsm == 1'b1) begin
        					command_writer.action = BUFFER_WRITE;
        					if (word_counter == word_counter_t'(0)) begin
        						command_in_pending_next = 1'b0;
        					end
        					if (command_writer.ready == 1'b1) begin
        						get_writer_access_fsm = 1'b0;
        						if (word_counter == word_counter_t'(0)) begin
        							state_next = NO_COMMAND;
        						end
        						else begin
        							word_counter_next = word_counter - word_counter_t'(1);
        							state_next = WAIT_FOR_NEXT_WORD;
        						end
        					end
                        end
                    end
    			end
    			
    			WAIT_FOR_NEXT_WORD: begin
                    if (ecc_error_rx_data.double_error == 1'b1) begin
                        state_next = NO_COMMAND;
                        command_in_pending_next = 1'b0;
                        forbid_writing_to_buffer_and_invalidate_at_the_end_next = 1'b1;
                    end
                    else begin
        				if ((i_received_word == 1'b1) || (handle_received_word == 1'b1)) begin
        					`if_writing_allowed_begin
        						handle_received_word_next = 1'b0;
        						state_next = WRITE_COMMAND;
        						get_writer_access_fsm = 1'b1;
        					end
                        end 
                    end
    			end
    			
    			/*###   register read   ######################################################*/
    			READ_REGISTER: begin
                    if ((i_ram_initialized == 1'b0) && (address >= BASE_ADDR_RAM) && (address < BASE_ADDR_RAM + SIZE_RAM)) begin
    					o_set_fifo_data = 1'b1;
    					o_fifo_data = EMPTY_DATA;
    					state_next = READ_NEXT_REGISTER;
                    end
                    else begin
                        elip_spi_read.rd = 1'b1;
        				if (elip_spi_read.ready == 1'b1) begin
        					o_set_fifo_data = 1'b1;
        					o_fifo_data = elip_spi_read.data_read;
        					state_next = READ_NEXT_REGISTER;
                        end
                    end
    			end
    			READ_NEXT_REGISTER: begin
                    if (i_alignment_error) begin
                        state_next = NO_COMMAND;
                        command_in_pending_next = 1'b0;
                        expect_command_nibble_next = 1'b0;
                        o_command_incomplete = 1'b1;
                        o_clear_fifo = 1'b1;
                    end
                    else begin
        				if ((i_received_word == 1'b1) || (handle_received_word == 1'b1)) begin
        					if ((command.command != REG_READ) || (ecc_error_rx_data.double_error == 1'b1)) begin
            						state_next = NO_COMMAND;
            						command_in_pending_next = 1'b0;
                                    o_command_incomplete = 1'b1;
                                    expect_command_nibble_next = 1'b0;
                                    o_clear_fifo = 1'b1;
                                    // no handle_received_word_next = 1'b0 since the next command must be executed
                            end
                            else begin
            					handle_received_word_next = 1'b0;
            					if ((command.data == '0)) begin
            						state_next = NO_COMMAND;
            						command_in_pending_next = 1'b0;
                                    expect_command_nibble_next = 1'b0;
            					end
            					else begin
            						address_next = {4'b0, command.data};
            						store_address = 1'b1;
            						state_next = READ_REGISTER;
                                end
                            end
                        end
                    end
    			end
    			
    			/*###   read CRM packets   ######################################################*/
    			READ_CRM_CHANNEL: begin // to select correct channel
                    if ((command.command != DSI_READ_CRM_DATA) || (i_alignment_error == 1'b1) || (ecc_error_rx_data.double_error == 1'b1)) begin
                        state_next = NO_COMMAND;
                        expect_command_nibble_next = 1'b0;
                        o_command_incomplete = 1'b1;
                        o_clear_fifo = 1'b1;
                    end
                    else begin
        				handle_received_word_next = 1'b0;
        				if (current_channel > current_channel_t'(DSI_CHANNELS-1)) begin  // all channels read
        					if (i_tx_data_available == 1'b0) begin // everything is sent
        						state_next = NO_COMMAND;
                                expect_command_nibble_next = 1'b0;
        						command_in_pending_next = 1'b0;
        					end
        				end
        				else begin
        					if (packet_read_command_info.channels[current_channel[1:0]] == 1'b1) begin
        						state_next = READ_CRM_DATA;
        					end
        					else begin
        						current_channel_next = current_channel + current_channel_t'(1);
        					end
                        end
                    end
    			end
    			READ_CRM_DATA: begin
    				if (i_fifo_full == 1'b0) begin
    					crm_packet_reader.get_data = 1'b1;
    					if (crm_packet_reader.got_data == 1'b1) begin
    						o_set_fifo_data = 1'b1;
    						o_fifo_data = crm_packet_reader.data;
    					end
    				end
    				if (crm_packet_reader.finished == 1'b1) begin
    					state_next = READ_CRM_FINISH;
    					current_channel_next = current_channel + current_channel_t'(1);
    				end
    				if ((command.command != DSI_READ_CRM_DATA) || (i_alignment_error == 1'b1) || (ecc_error_rx_data.double_error == 1'b1)) begin
    					crm_packet_reader.abort = 1'b1;
    					state_next = NO_COMMAND;
                        expect_command_nibble_next = 1'b0;
    					o_command_incomplete = 1'b1;
                        o_clear_fifo = 1'b1;
    				end
    			end
    			
    			READ_CRM_FINISH: begin
    				if (i_fifo_full == 1'b0) begin
    					state_next = READ_CRM_CHANNEL;
    				end
                    if ((command.command != DSI_READ_CRM_DATA) || (i_alignment_error == 1'b1) || (ecc_error_rx_data.double_error == 1'b1)) begin
    					state_next = NO_COMMAND;
                        expect_command_nibble_next = 1'b0;
    					o_command_incomplete = 1'b1;
                        o_clear_fifo = 1'b1;
    				end
    			end
    			
    			/*###   read PDCM frames   ######################################################*/
                READ_PDCM_CHANNEL: begin // to select correct channel
                    if ((command.command != DSI_READ_PDCM_DATA) || (i_alignment_error == 1'b1) || (ecc_error_rx_data.double_error == 1'b1)) begin
                        pdcm_frame_reader.abort = 1'b1;
                        state_next = NO_COMMAND;
                        expect_command_nibble_next = 1'b0;
                        o_command_incomplete = 1'b1;
                        o_clear_fifo = 1'b1;
                        command_in_pending_next = 1'b0;
                    end
                    else begin
                        handle_received_word_next = 1'b0;
                        if (current_channel > current_channel_t'(DSI_CHANNELS-1)) begin  // all channels read
                            if (i_some_tx_data_in_fifo == 1'b0) begin // everything is sent
                                state_next = NO_COMMAND;
                                expect_command_nibble_next = 1'b0;
                                command_in_pending_next = 1'b0;
                            end
                        end
                        else begin
                            if (packet_read_command_info.channels[current_channel[1:0]] == 1'b1) begin
                                state_next = READ_PDCM_FRAME;
                            end
                            else begin
                                current_channel_next = current_channel + current_channel_t'(1);
                            end
                        end
                    end
                end
                
                READ_PDCM_FRAME: begin
                    if (i_no_tdma_scheme_defined[current_channel] == 1'b1) begin
                        if (i_fifo_full == 1'b0) begin
                            state_next = READ_PDCM_CHANNEL;
                            o_set_fifo_data = 1'b1;
                            o_fifo_data = EMPTY_DATA;
                            current_channel_next = current_channel + current_channel_t'(1);
                        end
                    end
                    else begin
                        if (pdcm_frame_reader.finished == 1'b1) begin // all data read
                            if (current_channel > current_channel_t'(DSI_CHANNELS-1)) begin  // all channels read
                                state_next = READ_PDCM_FINISH;
                            end
                            else begin
                                state_next = READ_PDCM_CHANNEL;
                                current_channel_next = current_channel + current_channel_t'(1);
                            end
                        end
                        else begin // read data
                            if (i_fifo_full == 1'b0) begin
                                pdcm_frame_reader.get_data = 1'b1;
                                if (pdcm_frame_reader.got_data == 1'b1) begin
                                    o_set_fifo_data = 1'b1;
                                    o_fifo_data = pdcm_frame_reader.data;
                                end
                            end
                        end
                    end
                    if ((command.command != DSI_READ_PDCM_DATA) || (i_alignment_error == 1'b1) || (ecc_error_rx_data.double_error == 1'b1)) begin
                        pdcm_frame_reader.abort = 1'b1;
                        state_next = NO_COMMAND;
                        expect_command_nibble_next = 1'b0;
                        o_command_incomplete = 1'b1;
                        o_clear_fifo = 1'b1;
                        command_in_pending_next = 1'b0;
                    end
                end
                
                READ_PDCM_FINISH: begin
                    if (i_fifo_full == 1'b0) begin
                        state_next = READ_PDCM_CHANNEL;
                    end
                    if ((command.command != DSI_READ_PDCM_DATA) || (i_alignment_error == 1'b1)) begin
                        state_next = NO_COMMAND;
                        expect_command_nibble_next = 1'b0;
                        o_command_incomplete = 1'b1;
                        command_in_pending_next = 1'b0;
                        o_clear_fifo = 1'b1;
                    end
                end
    			
    			default: begin
    				o_hardware_fail = 1'b1;
    				state_next = NO_COMMAND;
                    expect_command_nibble_next = 1'b0;
    				command_in_pending_next = 1'b0;
    				forbid_writing_to_buffer_and_invalidate_at_the_end_next = 1'b1;
    			end
    		endcase
        end
		`ifdef VCS
		if ($time() > 10ns) begin
			assert	(!((address != address_next) && (store_address == 1'b0))) else $error("address(%h) cannot be stored with %h because store_address(%1b) is not 1", address, address_next, store_address);
			assert	(!((packet_read_command_info != packet_read_command_info_next) && (store_packet_info == 1'b0))) else $error("packet_read_command_info(%p) cannot be stored with %p because store_packet_info(%1b) is not 1", packet_read_command_info, packet_read_command_info_next, store_packet_info);
		end
		`endif
	end
	
	crm_packet_reader i_crm_packet_reader (
		.clk_rst    (clk_rst                     ),
		.reader     (crm_packet_reader.slave     ),
		.data_reader(dsi3_crm_data_reader        ),
		.ecc_error  (crm_data_ecc_error.master   ),
        .o_hw_fail  (hw_fail_crm_packet_reader   )
	);
    
    data_t  current_tdma_frame_word_counter;
    assign  current_tdma_frame_word_counter = (int'(current_channel) < DSI_CHANNELS) ? i_tdma_frame_word_count[current_channel] : '0;
	
	pdcm_frame_reader i_pdcm_frame_reader (
		.clk_rst                (clk_rst                     ),
		.reader                 (pdcm_frame_reader.slave     ),
		.data_reader            (dsi3_pdcm_data_reader       ),
        .ecc_error              (pdcm_data_ecc_error.master  ),
        .i_tdma_frame_word_count(current_tdma_frame_word_counter)
	);
	
    assign  elip_spi_read.addr  = address;
	assign	elip_spi_read.wr = 1'b0;
	assign  elip_spi_read.data_write.data = '0;
	assign  elip_spi_read.data_write.ecc  = ECC_FOR_DATA_0;
	
endmodule