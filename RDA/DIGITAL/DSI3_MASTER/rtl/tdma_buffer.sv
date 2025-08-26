/*------------------------------------------------------------------------------
 * File          : tdma_buffer.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

module tdma_buffer #(
		parameter	shortint BASE_ADDRESS
	)(
		clk_reset_if.slave		clk_rst,
		elip_full_if.master		elip,
		tdma_interface.slave	tdma,
        ecc_error_if.master     ecc_error,
        output  logic           o_hw_fail
	);
	
	import project_pkg::*;
	import tdma_pkg::*;
    `include "ecc_register_inc.sv"
	
	tmda_buffer_state_t state, state_next;
	tdma_packet_ecc_t	packet;
	tdma_header_ecc_t	header;
	logic[3:0]		packet_index, packet_index_next;
    
    logic   store_earliest, store_latest, store_info;
    logic   store_period, store_packet_count;
    
    //#####   ECC decoder   ############################################################
    ecc_error_if    ecc_error_state();
    logic[2:0]  state_out;
    ecc_register #(.WIDTH(3), .RESET_VAL(IDLE)) i_ecc_register_state (
        .clk_rst   (clk_rst   ),
        .i_waccess (1'b1 ),
        .i_raccess (1'b1 ),
        .i_wdata   (state_next),
        .o_rdata   (state_out ),
        .o_ecc_corr(ecc_error_state.single_error),
        .o_ecc_fail(ecc_error_state.double_error)
    );
    assign  state = tmda_buffer_state_t'(state_out);
    
    `ecc_register(packet_index, 4, '0)
    
    assign  ecc_error.single_error = ecc_error_state.single_error | packet_index_ecc_corr;
    assign  ecc_error.double_error = ecc_error_state.double_error | packet_index_ecc_fail;
    
    //#####   FSM   ####################################################################
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (!clk_rst.rstn) begin
			packet	<= EMPTY_TDMA_PACKET;
			header	<= EMPTY_TDMA_HEADER;
		end
		else begin
            if (store_packet_count == 1'b1) header.packet_count <= elip.data_read;
            if (store_period == 1'b1)       header.period       <= elip.data_read;
            if (store_earliest == 1'b1)     packet.earliest     <= elip.data_read;
            if (store_latest == 1'b1)       packet.latest       <= elip.data_read;
            if (store_info == 1'b1)         packet.info         <= elip.data_read;
		end
    end
    
	`define elip_read(_address_)	elip.addr = _address_; \
		elip.rd = 1'b1;
	
	always_comb begin
		elip.addr = BASE_ADDRESS;
		elip.rd = 1'b0;
		elip.wr = 1'b0;
		elip.data_write = EMPTY_DATA;
		state_next = state;
		packet_index_next = packet_index;
		tdma.acknowledge = 1'b0;
        
        store_earliest  = 1'b0;
        store_latest    = 1'b0;
        store_info      = 1'b0;
        
        store_period        = 1'b0;
        store_packet_count  = 1'b0;
        
        o_hw_fail = 1'b0;
        
		case (state)
			IDLE: begin
				if (tdma.request == 1'b1) begin
					case (tdma.target)
						HEADER: begin
							state_next = HEADER1;
						end
						PACKET: begin
							state_next = PACKET_EARLIEST;
							packet_index_next = tdma.index;
						end
					endcase
				end
			end
			HEADER1: begin
				elip.addr = BASE_ADDRESS;
				if (tdma.write == 1'b1) begin
					elip.wr = 1'b1;
					elip.data_write = tdma.header_to_buffer.packet_count;
				end
				else begin
					elip.rd = 1'b1;
				end
				if (elip.ready == 1'b1) begin
					state_next = HEADER2;
					if (tdma.write == 1'b0)
						store_packet_count = 1'b1;
				end
			end
			HEADER2: begin
				elip.addr = BASE_ADDRESS+data_t'(1);
				if (tdma.write == 1'b1) begin
					elip.wr = 1'b1;
					elip.data_write = tdma.header_to_buffer.period;
				end
				else begin
					elip.rd = 1'b1;
				end
				if (elip.ready == 1'b1) begin
					state_next = IDLE;
					tdma.acknowledge = 1'b1;
					if (tdma.write == 1'b0)
                        store_period = 1'b1;
				end
			end
			PACKET_EARLIEST: begin
				elip.addr = BASE_ADDRESS+16'(8'(packet_index)*8'd3)+16'd2;
				if (tdma.write == 1'b1) begin
					elip.wr = 1'b1;
					elip.data_write = tdma.packet_to_buffer.earliest;
				end
				else begin
					elip.rd = 1'b1;
				end
				if (elip.ready == 1'b1) begin
					state_next = PACKET_LATEST;
					if (tdma.write == 1'b0)
                        store_earliest = 1'b1;
				end
			end
			PACKET_LATEST: begin
				elip.addr = BASE_ADDRESS+16'(8'(packet_index)*8'd3)+16'd3;
				if (tdma.write == 1'b1) begin
					elip.wr = 1'b1;
					elip.data_write = tdma.packet_to_buffer.latest;
				end
				else begin
					elip.rd = 1'b1;
				end
				if (elip.ready == 1'b1) begin
					state_next = PACKET_INFO;
					if (tdma.write == 1'b0)
                        store_latest = 1'b1;
				end
			end
			PACKET_INFO: begin
				elip.addr = BASE_ADDRESS+16'(8'(packet_index)*8'd3)+16'd4;
				if (tdma.write == 1'b1) begin
					elip.wr = 1'b1;
					elip.data_write = tdma.packet_to_buffer.info;
				end
				else begin
					elip.rd = 1'b1;
				end
				if (elip.ready == 1'b1) begin
					state_next = ACKNOWLEDGE;
					if (tdma.write == 1'b0)
                        store_info = 1'b1;
				end
			end
			ACKNOWLEDGE: begin
				tdma.acknowledge = 1'b1;
				state_next = IDLE;
			end
			
			default: begin
				state_next = IDLE;
                o_hw_fail = 1'b1;
			end
        endcase
        if (ecc_error.double_error == 1'b1) begin
            state_next = IDLE;
            o_hw_fail = 1'b1;
            tdma.acknowledge = 1'b1;
        end
	end
	
	assign	tdma.packet_from_buffer = packet;
	assign	tdma.header_from_buffer = header;
	
endmodule