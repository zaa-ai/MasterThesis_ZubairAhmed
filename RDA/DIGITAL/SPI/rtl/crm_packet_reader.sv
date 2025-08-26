/*------------------------------------------------------------------------------
 * File          : crm_packet_reader.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Mar 6, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

module crm_packet_reader #() (
		clk_reset_if.slave      clk_rst,
		packet_reader_if.slave	reader,
		buffer_reader_if.master data_reader,
		ecc_error_if.master     ecc_error,
        output  logic           o_hw_fail
	);
	
	import spi_implementation_pkg::*;
	import project_pkg::*;
	import buffer_if_pkg::*;
	
	typedef	enum logic[1:0] {IDLE, READ_HEADER, READ_DATA, FINISH_PACKET} packet_reader_state_t;
	packet_reader_state_t	state, state_next;
	
	typedef logic[1:0] word_counter_t;
	word_counter_t	word_counter, word_counter_next;
	word_counter_t	current_packet_header_word_count, current_packet_header_word_count_next;
	
	// @SuppressProblem -type partially_unread_data -count 1 -length 1
	PACKET_STAT_t	crm_packet_header;
	data_t			data_corrected;
	
	packet_state_e	packet_state;
	
	/*###   ECC_DECCODER - CRM data reader  #######################################*/
	ecc_decoder #(
		.DATA_WIDTH(DATA_WIDTH),
		.ECC_WIDTH (ECC_WIDTH )
	) i_ecc_dec_crm_rx_data (
		.i_correct_n(1'b0                   ),
		.i_data     (data_reader.data.data  ),
		.i_ecc      (data_reader.data.ecc   ),
		.o_data     (data_corrected         ),
		.o_ecc_cor  (ecc_error.single_error ),
		.o_ecc_err  (ecc_error.double_error ));
	
	assign	crm_packet_header = data_corrected;
	
	/*###   FSM   #################################################################*/
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			state	<= IDLE;
			word_counter <= '0;
			current_packet_header_word_count <= '0;
		end
		else begin
			state	<= state_next;
			word_counter <= word_counter_next;
			current_packet_header_word_count <= current_packet_header_word_count_next;
		end
	end
	
	always_comb begin
		state_next = state;
		current_packet_header_word_count_next = current_packet_header_word_count;
		word_counter_next = word_counter;
		reader.finished = 1'b0;
		reader.got_data = 1'b0;
		
		data_reader.action = IDLE_READ;
		data_reader.step = '0;
        
        o_hw_fail = 1'b0;
        reader.data = data_reader.data;
		
		case(state)
			IDLE: begin
				if (reader.get_data == 1'b1) begin
					state_next = READ_HEADER;
					word_counter_next = '0;
				end
			end
			READ_HEADER: begin
				data_reader.action = BUFFER_READ;
				if (data_reader.ready == 1'b1) begin
					reader.got_data = 1'b1;
					
					state_next = READ_DATA;
					if (crm_packet_header.SYMBOL_COUNT > 8'd3) begin
						if (crm_packet_header.SYMBOL_COUNT == 8'd4) begin
							current_packet_header_word_count_next = 2'd1;
						end
						else begin
							current_packet_header_word_count_next = 2'd2;
						end
					end
					else begin
						current_packet_header_word_count_next = '0;
					end
					
					word_counter_next = '0;
                end
                if (reader.abort == 1'b1) begin
                    state_next = FINISH_PACKET;
                end
			end
			READ_DATA: begin
				case (packet_state)
					PACKET_ONGOING: begin
						if (reader.get_data == 1'b1) begin
							data_reader.action = BUFFER_READ;
							if (data_reader.ready == 1'b1) begin
								reader.got_data = 1'b1;
								word_counter_next = word_counter + word_counter_t'(1);
							end
						end
						if (reader.abort == 1'b1) begin
							state_next = FINISH_PACKET;
						end
					end
					PACKET_FILL_ZERO: begin
						if (reader.get_data == 1'b1) begin
                            reader.data = EMPTY_DATA;
							reader.got_data = 1'b1;
							word_counter_next = word_counter + word_counter_t'(1);
						end
						if (reader.abort == 1'b1) begin
							state_next = IDLE;
						end
					end
					PACKET_FINISHED: begin
						state_next = IDLE;
						reader.finished = 1'b1;
                    end
                    default: begin
                        state_next = IDLE;
                        reader.finished = 1'b1;
                        o_hw_fail = 1'b1;
                    end
				endcase
			end
			FINISH_PACKET: begin
				data_reader.action = BUFFER_MOVE_POINTER;
				data_reader.step = 16'(current_packet_header_word_count - word_counter);
				if (data_reader.ready == 1'b1) begin
					state_next = IDLE;
				end
			end
		endcase
	end
	
	always_comb begin
		packet_state = PACKET_ONGOING;
		if (word_counter < 2'd2) begin
			if (word_counter < current_packet_header_word_count) begin
				packet_state = PACKET_ONGOING;
			end
			else begin
				packet_state = PACKET_FILL_ZERO;
			end
		end
		else begin
			packet_state = PACKET_FINISHED;
		end
	end
	
endmodule