/**
 * Module: buffer
 * 
 * Module implementing a ring buffer with (2^BUFFER_SIZE)-1 cells
 */
module buffer import project_pkg::*; import buffer_if_pkg::*; #(
		parameter 	elip_addr_t BASE_ADDR = 0,
		parameter	ADDR_WIDTH = 16,
		parameter	elip_addr_t BUFFER_OFFSET_ADDRESS,
		parameter	elip_addr_t BUFFER_SIZE,
		parameter	bit			PRIORITY_READ = 1'b0 
	)(
			clk_reset_if.slave clk_rst,
			buffer_reader_if.slave	reader,
			buffer_writer_if.slave	writer,
		
			elip_full_if.master elip,
			elip_if.slave		elip_registers,
			output	elip_data_t	o_elip_registers_data_out,
			output	logic		o_data_available,
			ecc_error_if.master	ecc_error
	);
	
	localparam BUFFER_POINTER_WIDTH = $clog2(BUFFER_SIZE);
	typedef logic[BUFFER_POINTER_WIDTH-1:0] buffer_pointer_t;
	typedef logic[BUFFER_POINTER_WIDTH:0] number_of_cells_t;
	
	`include "ring_buffer_registers_if_inst.sv"
	
	ring_buffer_registers #(
		.base_addr                                (BASE_ADDR                                      ), 
		.addr_width                               (ADDR_WIDTH                                     )
	) i_ring_buffer_registers (
		.clk_rst                                  (clk_rst                                        ), 
		.addr                                     (elip_registers.addr                            ), 
		.rd                                       (elip_registers.rd                              ), 
		.data_out                                 (o_elip_registers_data_out                      ), 
		.ring_buffer_registers_BUF_VALID_COUNT    (ring_buffer_registers_BUF_VALID_COUNT.master   ), 
		.ring_buffer_registers_BUF_FREE           (ring_buffer_registers_BUF_FREE.master          ), 
		.ring_buffer_registers_BUF_READ_POINTER   (ring_buffer_registers_BUF_READ_POINTER.master  ), 
		.ring_buffer_registers_BUF_WRITE_POINTER  (ring_buffer_registers_BUF_WRITE_POINTER.master ), 
		.ring_buffer_registers_BUF_VALID_POINTER  (ring_buffer_registers_BUF_VALID_POINTER.master ));
	
	/*###   signal and interface defintions   ######################################################*/
	buffer_pointer_t	valid, valid_next, write, write_next, read, read_next;
	logic				empty, full, nearly_full;
	
	typedef enum logic[8:0] {
		IDLE			= 9'h001,
		READING			= 9'h002,
		WRITING			= 9'h004,
		WRITING_FIRST	= 9'h008, 
		VALIDATING		= 9'h010, 
		INVALIDATING	= 9'h020, 
		CLEARING		= 9'h040, 
		MOVING_POINTER	= 9'h080,
		CLEAR_AND_INVALIDATE_NEXT = 9'h100
	} buffer_access_state_e;
	logic[8:0]	int_state_fsm_for_reassigment;
	buffer_access_state_e	access_state, access_request, state_fsm, state_fsm_next;
	
	number_of_cells_t	number_of_free_cells;
	number_of_cells_t	number_of_valid_cells;
	
	logic	ready;
	logic	invalid_memory_content, invalid_memory_content_next;
	
	/*###   register assignments   ######################################################*/
	assign	ring_buffer_registers_BUF_VALID_POINTER.VALID_POINTER_in = elip_addr_t'(valid) + BUFFER_OFFSET_ADDRESS;
	assign	ring_buffer_registers_BUF_READ_POINTER.READ_POINTER_in = elip_addr_t'(read) + BUFFER_OFFSET_ADDRESS;
	assign	ring_buffer_registers_BUF_WRITE_POINTER.WRITE_POINTER_in = elip_addr_t'(write) + BUFFER_OFFSET_ADDRESS;
	assign	ring_buffer_registers_BUF_FREE.FREE_in = elip_addr_t'(number_of_free_cells);
	assign	ring_buffer_registers_BUF_VALID_COUNT.VALID_COUNT_in = 12'(number_of_valid_cells);
	
	/*###   buffer_pointer   ######################################################*/
	`include "ecc_register_inc.sv"
			
	`ecc_register(write, BUFFER_POINTER_WIDTH, 0)
	`ecc_register(read, BUFFER_POINTER_WIDTH, 0)
	`ecc_register(valid, BUFFER_POINTER_WIDTH, 0)
	
	logic	state_fsm_ecc_corr, state_fsm_ecc_fail;
	logic	state_has_changed;
	always_comb begin
		state_has_changed = 1'b0;
		if (state_fsm_next != state_fsm) begin
			state_has_changed = 1'b1;
		end
		else begin
			if ((state_fsm_ecc_corr == 1'b1) && (state_fsm_ecc_fail == 1'b0)) begin
				state_has_changed = 1'b1;
			end
		end
	end
	ecc_register #(
		.WIDTH       (9      ), 
		.RESET_VAL   (IDLE  )
		) i_state_fsm_ecc_register (
		.clk_rst     (clk_rst    ), 
		.i_waccess   (state_has_changed  ), 
		.i_raccess   (1'b1  ), 
		.i_wdata     (state_fsm_next    ), 
		.o_rdata     (int_state_fsm_for_reassigment), 
		.o_ecc_corr  (state_fsm_ecc_corr ), 
		.o_ecc_fail  (state_fsm_ecc_fail ));
	assign	state_fsm = buffer_access_state_e'(int_state_fsm_for_reassigment);
	
	/*###   ecc error interface   ######################################################*/
	assign	ecc_error.double_error = write_ecc_fail | read_ecc_fail | valid_ecc_fail | state_fsm_ecc_fail ;
	assign	ecc_error.single_error = write_ecc_corr | read_ecc_corr | valid_ecc_corr | state_fsm_ecc_corr ;
	
	/*###   buffer   ######################################################*/
	// choose access state between FSM and combinational input (access_request); as long as state is not left no new request can be accepted
	always_comb begin
		if (state_fsm == IDLE) begin
			access_state = access_request;
		end
		else begin
			access_state = state_fsm;
		end
	end
	
	// new request from interfaces
	generate
		if (PRIORITY_READ == 1'b1) begin : generate_priority_read
			always_comb begin 
				access_request = IDLE;
				if (reader.action != IDLE_READ) begin
					case(reader.action)
						BUFFER_MOVE_POINTER:	access_request = MOVING_POINTER;
						BUFFER_READ: 			access_request = READING;
                        default: begin
                            access_request = IDLE;
                        end
					endcase
				end
				else begin
					if (writer.action != IDLE_WRITE) begin
						case(writer.action)
							BUFFER_WRITE:		access_request = WRITING;
							BUFFER_VALIDATE:	access_request = VALIDATING;
							BUFFER_INVALIDATE:	access_request = INVALIDATING;
							BUFFER_WRITE_FIRST:	access_request = WRITING_FIRST;
							BUFFER_CLEAR:		access_request = CLEARING;
							BUFFER_CLEAR_AND_INVALIDATE_NEXT: 
												access_request = CLEAR_AND_INVALIDATE_NEXT;
                            default: begin
                                access_request = IDLE;
                            end
						endcase
					end
				end
			end
		end
		else begin : generate_priority_write
			always_comb begin 
				access_request = IDLE;
				if (writer.action != IDLE_WRITE) begin
					case(writer.action)
						BUFFER_WRITE:		access_request = WRITING;
						BUFFER_VALIDATE:	access_request = VALIDATING;
						BUFFER_INVALIDATE:	access_request = INVALIDATING;
						BUFFER_WRITE_FIRST:	access_request = WRITING_FIRST;
						BUFFER_CLEAR:		access_request = CLEARING;
						BUFFER_CLEAR_AND_INVALIDATE_NEXT: 
											access_request = CLEAR_AND_INVALIDATE_NEXT;
                        default: begin
                            access_request = IDLE;
                        end
					endcase
				end
				else begin
					if (reader.action != IDLE_READ) begin
						case(reader.action)
							BUFFER_MOVE_POINTER:	access_request = MOVING_POINTER;
							BUFFER_READ: 			access_request = READING;
                            default: begin
                                access_request = IDLE;
                            end
						endcase
					end
				end
			end
		end
	endgenerate
	
	always_comb begin
		state_fsm_next = state_fsm;
		case (state_fsm)
			IDLE: begin
				if (access_state != IDLE) begin
					if (ready != 1'b1) begin
						state_fsm_next = access_state;
					end
				end
			end
			default: begin
				if (ready == 1'b1) begin
					state_fsm_next = IDLE;
				end
			end
		endcase
	end
	
	always_comb begin
		ready = 1'b0;
		elip.wr = 1'b0;
		elip.rd = 1'b0;
		elip.addr = elip_addr_t'(read) + BUFFER_OFFSET_ADDRESS;
		
		read_next  = read;
		write_next = write;
		valid_next = valid;
		
		writer.ready = 1'b0;
		reader.data.data = '0;
		reader.data.ecc  = ECC_FOR_DATA_0;
		reader.ready = 1'b0;
		
		invalid_memory_content_next = invalid_memory_content;
		if (ecc_error.double_error == 1'b1) begin
			ready = 1'b1;
			write_next = '0;
			valid_next = '0;
			read_next = '0;
			if (write != valid) begin
				invalid_memory_content_next = 1'b1;
			end
		end
		else begin
			case(access_state)
				READING: begin
					if (empty == 1'b1) begin // read when empty
						reader.ready = 1'b1;
						reader.data.data = '0;
						reader.data.ecc  = ECC_FOR_DATA_0;
						ready = 1'b1;
					end
					else begin
						elip.wr = 1'b0;
						elip.rd = 1'b1;
						elip.addr = elip_addr_t'(read) + BUFFER_OFFSET_ADDRESS;
						ready = elip.ready;
						reader.ready = elip.ready;
						if (elip.ready == 1'b1) begin
							read_next = read + buffer_pointer_t'(1);
							reader.data = elip.data_read;
						end
					end
				end
				WRITING, WRITING_FIRST: begin
					if (full == 1'b1) begin //write when full --> nothing written + validation aborted!
						writer.ready = 1'b1;
						invalid_memory_content_next = 1'b1;
						ready = 1'b1;
					end
					else begin
						elip.wr = 1'b1;
						elip.rd = 1'b0;
						if (access_state == WRITING_FIRST)
							elip.addr = elip_addr_t'(valid) + BUFFER_OFFSET_ADDRESS;
						else
							elip.addr = elip_addr_t'(write) + BUFFER_OFFSET_ADDRESS;
						ready = elip.ready;
						writer.ready = elip.ready;
						if (elip.ready == 1'b1) begin
							if (access_state == WRITING) begin
								write_next = write + buffer_pointer_t'(1);
							end
						end
					end
				end
				MOVING_POINTER: begin
					buffer_pointer_t step;
					ready = 1'b1;
					reader.ready = 1'b1;
					if (data_t'(number_of_valid_cells) >= reader.step) begin // limiting steps
						step = buffer_pointer_t'(reader.step);
					end
					else begin
						step = buffer_pointer_t'(number_of_valid_cells);
					end
					read_next = read + buffer_pointer_t'(step);
				end
				VALIDATING: begin
					invalid_memory_content_next = 1'b0;
					ready = 1'b1;
					writer.ready = 1'b1;
					if (invalid_memory_content == 1'b1) begin // invalidate
						write_next = valid;
					end
					else begin
						valid_next = write;
					end
				end
				INVALIDATING: begin
					invalid_memory_content_next = 1'b0;
					ready = 1'b1;
					writer.ready = 1'b1;
					write_next = valid;
				end
				CLEARING: begin
					writer.ready = 1'b1;
					ready = 1'b1;
					read_next = valid;
				end
				CLEAR_AND_INVALIDATE_NEXT: begin
                    invalid_memory_content_next = 1'b1;
					writer.ready = 1'b1;
					ready = 1'b1;
					read_next = valid;
				end
				IDLE: begin
					
				end
				default: begin
					ready = 1'b1;
					invalid_memory_content_next = 1'b1;
				end
			endcase
		end
	end
	
	assign elip.data_write.data = writer.data.data;
	assign elip.data_write.ecc = writer.data.ecc;
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			invalid_memory_content <= 1'b0;
		end
		else begin
			invalid_memory_content <= invalid_memory_content_next;
		end
	end
	
	/*###   buffer status flags   ######################################################*/
	always_comb begin
		empty = 1'b0;
		if(number_of_valid_cells == '0)
			empty = 1'b1;
	end
	
	always_comb begin
		full = 1'b0;
		if(number_of_free_cells == '0)
			full = 1'b1;
	end
	
	always_comb begin
		nearly_full = 1'b0;
		if (number_of_free_cells < number_of_cells_t'(BUFFER_SIZE/elip_addr_t'(4))) begin
			nearly_full = 1'b1;
		end
	end
	
	assign	reader.empty = empty;
	assign	writer.full = full;
	assign 	writer.nearly_full = nearly_full;
	assign	o_data_available = (number_of_valid_cells > number_of_cells_t'(0)) ? 1'b1 : 1'b0;
	
	always_comb begin
		if (write >= read) begin
			number_of_free_cells = number_of_cells_t'(BUFFER_SIZE) - number_of_cells_t'(write - read) - number_of_cells_t'(1);
		end
		else begin
			number_of_free_cells = number_of_cells_t'(read - write) - number_of_cells_t'(1);
		end
	end
	
	always_comb begin
		if (valid >= read) begin
			number_of_valid_cells = number_of_cells_t'(valid - read);
		end
		else begin
			number_of_valid_cells = number_of_cells_t'(BUFFER_SIZE) - number_of_cells_t'(read - valid);
		end
	end
	
	`ifdef VCS
		
		clocking cb @(posedge clk_rst.clk);
			property write_when_full_no_change;
				(writer.action==BUFFER_WRITE) and full and elip.ready |=> $stable(write);
			endproperty 
			
		endclocking
		
		//TODO: add assertions for addresses (incrment + overlap) number of free cells ,...
//		as_write_when_full_no_change : assert property (cb.write_when_full_no_change) else $error("write_when_full_no_change: Write did change while full and data written to buffer!");
//		cov_write_when_full_no_change : cover property (cb.write_when_full_no_change);
		
		initial begin
			if (2**BUFFER_POINTER_WIDTH != int'(BUFFER_SIZE))
				// @SuppressProblem -type dead_code_auto_procedure -count 1 -length 1
				$fatal("Buffer pointer width is not set correct! Got %1d for a buffer size of %1d", BUFFER_POINTER_WIDTH, BUFFER_SIZE);
		end
	`endif
	
endmodule
