/*------------------------------------------------------------------------------
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Feb 17, 2023
 * Description   : manages TDMA scheme usage
 * 					- writing TDMA scheme
 * 					- validating TDMA schemes
 * 					- preparing usage for dsi3_core
 *------------------------------------------------------------------------------*/
module tdma_manager import tdma_pkg::*; import project_pkg::*; #(
		parameter	shortint	BASE_ADDRESS
	)(
		clk_reset_if.slave		clk_rst,
		elip_full_if.master		elip,
		tdma_writer_if.slave	writer,
        tdma_reader_if.slave    reader,
        
        ecc_error_if.master     ecc_error,
		
        input	data_t			i_period,
        input   logic           i_invalidate_tdma_scheme,
    `ifdef VCS
        input   logic           i_tick_1us,
        input   data_t          i_current_time_in_period,
    `endif
		output	logic			o_tdma_scheme_valid,
        output  data_t          o_tdma_frame_word_count,
        
        output  logic           o_hw_fail,
        output  logic           o_clear_data_buffer
	);
	
	import spi_implementation_pkg::*;
	
	tdma_interface tdma ();
	
	tdma_information_package_ecc_t	tdma_info_ecc;
	tdma_information_package_t	    tdma_info;
	
    
    ecc_error_if ecc_error_tdma_buffer();
    logic   hw_fail_tdma_buffer;
    logic   hw_fail;
    
	tdma_buffer #(.BASE_ADDRESS(BASE_ADDRESS)) u_tdma_buffer (
		.clk_rst(clk_rst),
		.elip   (elip   ),
		.tdma   (tdma.slave   ),
        .ecc_error (ecc_error_tdma_buffer.master),
        .o_hw_fail (hw_fail_tdma_buffer)
    );
    
    data_t  frame_word_count, frame_word_count_next;
	
	tdma_manager_state_t	state, state_next;
	tdma_manager_state_t	state_to_branch, state_to_branch_next;
	tdma_packet_index_t		packet_counter_for_read, packet_counter_for_read_next;
	tdma_packet_index_t		next_packet_index_for_read, current_packet_index; // no ECC since it's calucated from ECC corrected FF
	
	logic					tdma_scheme_valid_next;
	logic					temp_tdma_scheme_valid, temp_tdma_scheme_valid_next;
    logic                   store_header, store_new_packet;
    logic                   validate, validate_next;
    
    assign  o_tdma_frame_word_count = frame_word_count;
    
    //##########################   TDMA visualization   ################################
    `ifdef VCS
        tdma_scheme_visualizer u_tdma_scheme_visualizer (
            .clk_rst   (clk_rst   ),
            .i_tick_1us(i_tick_1us),
            .i_current_time_in_period(i_current_time_in_period)
        );
    `endif
    
    //#####   ECC FFs   ################################################################
    logic   [3:0] packet_counter_for_read_corrected;
    ecc_error_if  ecc_error_packet_counter_for_read();
    ecc_register #(.WIDTH(4), .RESET_VAL('0)) i_ecc_register_packet_counter (
        .clk_rst   (clk_rst   ),
        .i_waccess (1'b1 ),
        .i_raccess (1'b1 ),
        .i_wdata   (packet_counter_for_read_next   ),
        .o_rdata   (packet_counter_for_read_corrected   ),
        .o_ecc_corr(ecc_error_packet_counter_for_read.single_error),
        .o_ecc_fail(ecc_error_packet_counter_for_read.double_error)
    );
    assign  packet_counter_for_read = packet_counter_for_read_corrected;
    
    ecc_error_if    ecc_error_state();
    logic[2:0]  state_out;
    ecc_register #(.WIDTH(3), .RESET_VAL(S_IDLE)) i_ecc_register_fsm_state (
        .clk_rst   (clk_rst   ),
        .i_waccess (1'b1 ),
        .i_raccess (1'b1 ),
        .i_wdata   (state_next),
        .o_rdata   (state_out ),
        .o_ecc_corr(ecc_error_state.single_error),
        .o_ecc_fail(ecc_error_state.double_error)
    );
    assign  state = tdma_manager_state_t'(state_out);
    
    ecc_error_if    ecc_error_state_to_branch();
    logic[2:0]  state_to_branch_out;
    ecc_register #(.WIDTH(3), .RESET_VAL(S_IDLE)) i_ecc_register_fsm_state_to_branch (
        .clk_rst   (clk_rst   ),
        .i_waccess (1'b1 ),
        .i_raccess (1'b1 ),
        .i_wdata   (state_to_branch_next),
        .o_rdata   (state_to_branch_out ),
        .o_ecc_corr(ecc_error_state_to_branch.single_error),
        .o_ecc_fail(ecc_error_state_to_branch.double_error)
    );
    assign  state_to_branch = tdma_manager_state_t'(state_to_branch_out);
    
    //#####   ECC decoder   ############################################################
    ecc_error_if ecc_error_tdma_info ();
    ecc_error_if ecc_error_tdma_info_static ();
    tdma_ecc_check i_tdma_ecc_check (
        .i_packet     (tdma_info_ecc.current_packet),
        .i_packet_next(tdma_info_ecc.next_packet),
        .i_header     (tdma_info_ecc.header),
        .o_packet     (tdma_info.current_packet),
        .o_packet_next(tdma_info.next_packet),
        .o_header     (tdma_info.header),
        .ecc_error    (ecc_error_tdma_info_static.master )
    );
    
    ecc_edge_detection i_ecc_edge_detection_tdma_info (
        .clk_rst(clk_rst),
        .ecc_in (ecc_error_tdma_info_static.slave ),
        .ecc_out(ecc_error_tdma_info.master)
    );
    
    ecc_error_if    ecc_error_packet_index();
    // @SuppressProblem -type partially_unread_data -count 1 -length 1
    data_t packet_index_corrected;
    logic   ecc_error_packet_index_single_error,  ecc_error_packet_index_double_error;
    logic   check_ecc_error_packet_index;
    ecc_decoder #(.DATA_WIDTH(DATA_WIDTH), .ECC_WIDTH(ECC_WIDTH)) i_ecc_decoder_packet_index (
        .i_correct_n(1'b0),
        .i_data     (writer.packet_index.data),
        .i_ecc      (writer.packet_index.ecc ),
        .o_data     (packet_index_corrected     ),
        .o_ecc_cor  (ecc_error_packet_index_single_error  ),
        .o_ecc_err  (ecc_error_packet_index_double_error  )
    );
    
    assign  ecc_error_packet_index.single_error = ecc_error_packet_index_single_error & check_ecc_error_packet_index;
    assign  ecc_error_packet_index.double_error = ecc_error_packet_index_double_error & check_ecc_error_packet_index;
    
    //##################################################################################
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (!clk_rst.rstn) begin
            tdma_info_ecc   	<= '{EMPTY_TDMA_PACKET, EMPTY_TDMA_PACKET, EMPTY_TDMA_HEADER};
			o_tdma_scheme_valid <= 1'b0;
			temp_tdma_scheme_valid <= 1'b0;
            frame_word_count    <= '0;
            validate            <= '0;
		end
		else begin
			o_tdma_scheme_valid <= tdma_scheme_valid_next;
			temp_tdma_scheme_valid <= temp_tdma_scheme_valid_next;
            frame_word_count    <= frame_word_count_next;
            validate            <= validate_next;
            if (store_header)       tdma_info_ecc.header <= tdma.header_from_buffer;
            if (store_new_packet) begin
                tdma_info_ecc.current_packet    <= tdma_info_ecc.next_packet;
                tdma_info_ecc.next_packet       <= tdma.packet_from_buffer;
            end
		end
	end
	
	assign	tdma.packet_to_buffer		= writer.packet;
	assign	next_packet_index_for_read	= packet_counter_for_read + tdma_packet_index_t'(1);
	assign	current_packet_index		= packet_counter_for_read - tdma_packet_index_t'(2);
    
    tdma_packet_index_t tdma_header_packet_count;
    assign tdma_header_packet_count = tdma_info.header.packet_count.packet_count;
	
    `ifdef VCS
    always@(posedge clk_rst.clk) begin
        case (state)
            S_IDLE: begin
                if (writer.action != NO_ACTION) begin
                    case(writer.action)
                        VALIDATE : begin
                            u_tdma_scheme_visualizer.initialize();
                        end
                    endcase
                end
            end
            S_READ_FIRST_PACKET: begin
                u_tdma_scheme_visualizer.set_header(tdma_info.header);
            end
            S_VALIDATE: begin
                if (tdma_header_packet_count == '0) begin
                end
                else begin
                    if (current_packet_index < tdma_header_packet_count) begin
                        u_tdma_scheme_visualizer.set_packet(tdma_info.current_packet, int'(current_packet_index));
                    end
                end
            end
        endcase
    end
    `endif
    
   logic [6:0] word_count_of_next_packet;
   
   always_comb begin
       word_count_of_next_packet = {1'b0, tdma_info.next_packet.info.symbol_count[7:2]};
       if (tdma_info.next_packet.info.symbol_count[1:0] != '0)
           word_count_of_next_packet += 7'd1;
   end
    
	always_comb begin
		state_next = state;
		state_to_branch_next = state_to_branch;
		tdma.index = '0;
		tdma.write = 1'b0;
		tdma.request = 1'b0;
		tdma.header_to_buffer = '{0,0};
		tdma.target = PACKET;
		tdma_scheme_valid_next = o_tdma_scheme_valid;
		packet_counter_for_read_next = packet_counter_for_read;
		temp_tdma_scheme_valid_next = temp_tdma_scheme_valid;
		writer.acknowledge = 1'b0;
        reader.acknowledge = 1'b0;
        store_header = 1'b0;
        store_new_packet = 1'b0;
        frame_word_count_next = frame_word_count;
        validate_next = validate;
        check_ecc_error_packet_index = 1'b0;
        hw_fail = 1'b0;
        o_clear_data_buffer = 1'b0;
		
		case (state)
			S_IDLE: begin
                validate_next = 1'b0;
				if (writer.action != NO_ACTION) begin
					case(writer.action)
						WRITE_PACKET : begin
							state_next = S_WRITE_PACKET;
							tdma_scheme_valid_next = 1'b0;
						end
						WRITE_HEADER : begin
							state_next = S_WRITE_HEADER;
							tdma_scheme_valid_next = 1'b0;
						end
						VALIDATE : begin
							state_next = S_INITIALIZE;
							state_to_branch_next = S_VALIDATE;
							tdma_scheme_valid_next = 1'b0;
							temp_tdma_scheme_valid_next = 1'b1;
                            validate_next = 1'b1;
						end
					endcase
				end
				else begin
                    if(reader.action != NO_READ_ACTION) begin
					   case (reader.action)
                           READ_NEXT_PACKET: begin
                               state_next = S_READ_NEXT_PACKET;
                               state_to_branch_next = S_IDLE;
                           end
                           INITIALIZE: begin
                               state_next = S_INITIALIZE;
                               state_to_branch_next = S_IDLE;
                           end
                       endcase
                    end
                end
			end
			S_WRITE_HEADER: begin
				tdma.header_to_buffer = writer.header;
				tdma.request = 1'b1;
				tdma.write = 1'b1;
				tdma.target = HEADER;
				if (tdma.acknowledge == 1'b1) begin
					state_next = S_IDLE;
					writer.acknowledge = 1'b1;
				end
			end
			
			S_WRITE_PACKET: begin
                check_ecc_error_packet_index = 1'b1;
				tdma.index = packet_index_corrected[3:0];
				tdma.target = PACKET;
				tdma.write = 1'b1;
				tdma.request = 1'b1;
				if (tdma.acknowledge == 1'b1) begin
					state_next = S_IDLE;
					writer.acknowledge = 1'b1;
				end
			end
			
			S_INITIALIZE: begin
				tdma.request = 1'b1;
				tdma.target = HEADER;
				if (tdma.acknowledge == 1'b1) begin
                    store_header = 1'b1;
                    if (validate == 1'b1) frame_word_count_next = data_t'(1);
					state_next = S_READ_FIRST_PACKET;
					packet_counter_for_read_next = 4'd0;
				end
			end
			
			S_READ_FIRST_PACKET: begin
				tdma.request = 1'b1;
				tdma.target = PACKET;
				tdma.index = packet_counter_for_read;
				if (tdma.acknowledge == 1'b1) begin
                    store_new_packet = 1'b1;
					state_next = S_READ_NEXT_PACKET;
					packet_counter_for_read_next = next_packet_index_for_read;
//                    if (validate == 1'b1) frame_word_count_next = frame_word_count + 16'(word_count_of_next_packet) + data_t'(1);
				end
			end
			
			S_READ_NEXT_PACKET: begin
				tdma.request = 1'b1;
				tdma.target = PACKET;
				tdma.index = packet_counter_for_read;
				if (tdma.acknowledge == 1'b1) begin
                    store_new_packet = 1'b1;
					packet_counter_for_read_next = next_packet_index_for_read;
					state_next = state_to_branch;
                    if (validate == 1'b1) frame_word_count_next = frame_word_count + 16'(word_count_of_next_packet) + data_t'(1);
                    if (state_to_branch == S_IDLE)
                        reader.acknowledge = 1'b1;
				end
			end
			
			S_VALIDATE: begin
				if (tdma_header_packet_count == '0) begin
					tdma_scheme_valid_next = 1'b0;
					state_next = S_IDLE;
					writer.acknowledge = 1'b1;
                    frame_word_count_next = '0;
				end
				else begin
					if (current_packet_index < tdma_header_packet_count) begin
						if (tdma_info.current_packet.earliest == '0)
							temp_tdma_scheme_valid_next = 1'b0;
						if (tdma_info.current_packet.latest == '0)
							temp_tdma_scheme_valid_next = 1'b0;
						if (tdma_info.current_packet.info.symbol_count == '0)
							temp_tdma_scheme_valid_next = 1'b0;
						
						// check earliest N <= latest N
						if (tdma_info.current_packet.earliest > tdma_info.current_packet.latest)
							temp_tdma_scheme_valid_next = 1'b0;
						// check latest N < period
						if (tdma_info.current_packet.latest >= i_period)
							temp_tdma_scheme_valid_next = 1'b0;
						// check earliest N < period
						if (tdma_info.current_packet.earliest >= i_period)
							temp_tdma_scheme_valid_next = 1'b0;
						// symbol count packet N >= 4
						if (tdma_info.current_packet.info.symbol_count < 8'h04)
							temp_tdma_scheme_valid_next = 1'b0;
						if (current_packet_index < tdma_header_packet_count - 4'd1) begin
							// check latest N vs. earliest N+1
							if (tdma_info.current_packet.latest > tdma_info.next_packet.earliest)
								temp_tdma_scheme_valid_next = 1'b0;
						end
					end
					if (current_packet_index < tdma_header_packet_count-4'd1) begin
						state_next = S_READ_NEXT_PACKET;
						state_to_branch_next = S_VALIDATE;
					end
					else begin
						if (current_packet_index == tdma_header_packet_count-4'd1) begin
							tdma_scheme_valid_next = temp_tdma_scheme_valid_next;
						end
						else begin
							tdma_scheme_valid_next = temp_tdma_scheme_valid;
						end
						if (tdma_scheme_valid_next == 1'b1) begin
							state_next = S_INITIALIZE; // prepare for PDCM
							state_to_branch_next = S_IDLE;
						end
						else begin
							state_next = S_IDLE;
                            frame_word_count_next = '0;
						end
						writer.acknowledge = 1'b1;
                        validate_next = 1'b0;
					end
				end
            end
            default: begin
                state_next = S_IDLE;
                hw_fail = 1'b1;
                tdma_scheme_valid_next = 1'b0;
                writer.acknowledge = 1'b1;
                o_clear_data_buffer = 1'b1;
            end
        endcase
        
        if ((ecc_error.double_error == 1'b1) || (hw_fail_tdma_buffer == 1'b1)) begin
            state_next = S_IDLE;
            hw_fail = 1'b1;
            tdma_scheme_valid_next = 1'b0;
            writer.acknowledge = 1'b1;
            o_clear_data_buffer = 1'b1;
        end
        
        if(i_invalidate_tdma_scheme == 1'b1) begin
            tdma_scheme_valid_next = 1'b0;
        end
    end
    
    assign  o_hw_fail = hw_fail | hw_fail_tdma_buffer;
    
    assign  reader.header       = tdma_info.header;
    assign  reader.packet       = tdma_info.current_packet;
    assign  reader.packet_next  = tdma_info.next_packet;
    assign  reader.packet_index = current_packet_index;
    
    assign  ecc_error.single_error = ecc_error_tdma_buffer.single_error | ecc_error_tdma_info.single_error | ecc_error_packet_index.single_error | ecc_error_packet_counter_for_read.single_error | ecc_error_state.single_error | ecc_error_state_to_branch.single_error;
    assign  ecc_error.double_error = ecc_error_tdma_buffer.double_error | ecc_error_tdma_info.double_error | ecc_error_packet_index.double_error | ecc_error_packet_counter_for_read.double_error | ecc_error_state.double_error | ecc_error_state_to_branch.double_error;
	
endmodule