/**
 * Module: dsi3_symbol_builder
 * 
 * Module for building symbol from 3 chips and checking if for new packets
 */
module dsi3_symbol_builder import dsi3_pkg::*; (
		clk_reset_if.slave		clk_rst,
		dsi3_chip_if.slave		chip_in,
		input	logic			i_chip_ready,
		input	logic			i_enable,
		input	logic			i_stop_receiving,
		input	logic			i_next_chip_not_C0,
		output	logic			o_received_0_as_first,
		output	logic			o_symbol_ready,
		output	dsi3_symbol		o_symbol,
		output	logic			o_received_c0_after_packet
	);
	
	logic	[1:0]		chip_cnt, chip_cnt_nxt;
	logic				symbol_ready_nxt;
	dsi3_symbol			symbol_nxt;
	logic				symbol_ready;
	
	assign	o_symbol_ready = symbol_ready & i_enable;
	
	typedef enum logic {SYMBOL_IDLE, WAIT_FOR_NEXT_CHIP} symbol_state_e;
	
	symbol_state_e	state, state_next;
	
	logic	received_c0_after_packet, received_c0_after_packet_next;
	
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			chip_cnt		<= 2'd2;
			o_symbol		<= '{CX, CX, CX};
			symbol_ready	<= 1'b0;
			state			<= SYMBOL_IDLE;
			received_c0_after_packet <= 1'b0;
		end
		else begin
			chip_cnt		<= chip_cnt_nxt;
			o_symbol		<= symbol_nxt;
			state			<= state_next;
			received_c0_after_packet <= received_c0_after_packet_next;
			if (((i_chip_ready == 1'b1) && (i_enable == 1'b1)) || (symbol_ready == 1'b1))		// always reset if =1 except symbol is ready
				symbol_ready	<= symbol_ready_nxt;
		end
	end
	
	always_comb begin
		received_c0_after_packet_next = received_c0_after_packet;
		if (i_chip_ready == 1'b1) begin
			if (chip_in.chip == C0) begin
				if (chip_cnt == 2'd2) received_c0_after_packet_next = 1'b1;
			end
			else	received_c0_after_packet_next = 1'b0;
		end
		if ((i_stop_receiving == 1'b1) || (i_enable == 1'b0))
			received_c0_after_packet_next = 1'b0;
	end
	assign	o_received_c0_after_packet = received_c0_after_packet;
	
	
	always_comb begin
		chip_cnt_nxt = chip_cnt;
		symbol_nxt = o_symbol;
		if ((i_enable == 1'b1) && (i_stop_receiving == 1'b0)) begin
			if (i_chip_ready == 1'b1) begin								// if new chip available
				symbol_nxt[chip_cnt] = chip_in.chip;					// sample it as symbol
				if (chip_cnt == 2'd0) begin								// reset counter if counted to 0
					chip_cnt_nxt = 2'd2;
				end else begin											// 
					chip_cnt_nxt = chip_cnt - 2'd1;
				end
			end
		end else begin
			chip_cnt_nxt = 2'd2;
			symbol_nxt = '{CX, CX, CX};
		end
	end
	
	always_comb begin
		symbol_ready_nxt = 1'b0;
		o_received_0_as_first = 1'b0;
		state_next = state;
		case (state)
			SYMBOL_IDLE: begin
				if (i_enable == 1'b1) begin
					if (i_chip_ready == 1'b1) begin
						if (chip_cnt == 2'd0) begin
							if ((chip_in.chip == C0) && (o_symbol[2] == C0) && (o_symbol[1] == C0) && (i_next_chip_not_C0 == 1'b0)) begin
								state_next = WAIT_FOR_NEXT_CHIP;
							end
							else begin
								symbol_ready_nxt = 1'b1;
							end
						end
					end
				end
			end
			WAIT_FOR_NEXT_CHIP: begin
				if (i_enable == 1'b1) begin
					if (i_chip_ready == 1'b1) begin
						if ((i_next_chip_not_C0 == 1'b1)) begin
							symbol_ready_nxt = 1'b1;
						end
						else begin
							o_received_0_as_first = 1'b1;
						end
						state_next = SYMBOL_IDLE;
					end
				end
				if ((i_enable == 1'b0) || (i_stop_receiving == 1'b1)) begin
					state_next = SYMBOL_IDLE;
				end
			end
		endcase
	end
	
endmodule
