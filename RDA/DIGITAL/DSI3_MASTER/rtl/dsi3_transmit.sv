/**
 * Module: dsi3_transmit
 * 
 * Module for transmitting 32bit as DSI3 master
 */
module dsi3_transmit import dsi3_pkg::*; (
		clk_reset_if.slave clk_rst,
		//does not have to be ECC protected since it already has CRC protection. For DM and PDCM, pulses would be undetectable
		input	logic[31:0]	i_data,						// command input, taken over at start
		input	channel_mode_t	i_mode,					// mode of transmission
		
		input	logic		i_enable,					// disable transmitter
		input	logic		i_start,					// start transmission (tick only?)
		input	dsi3_bit_time_e	i_bit_time,
	
		output	logic		o_pend,						// transmission pending
		output	logic		o_tx,						// output stream at dsi3 driver
		output	logic		o_receive_mode_enable,	// switch DSI line to VSUP line with low impedance
		output	logic		o_acknowledge_start,
		output	logic		o_sample_time_base,			// event for sampling time base value (start of transmission)
		ecc_error_if.master ecc_error
	);
	
	logic	tick_1us;
	logic	start_transmission;
	
	tick_gen #(
		.ratio       (18      )
		) i_tick_gen_1us (
		.clk_rst     (clk_rst    ), 
		.reset_sync  (start_transmission ), 
		.tick_out    (tick_1us   ));

	/*###   internal data & bit counter   ######################################################*/
	logic[32:0]		data, data_next;
	logic[4:0]		length;
	logic[5:0]		bit_cnt, bit_cnt_nxt;
	logic			dsi3_oe, dsi3_oe_nxt;
	logic			transmit;
	channel_mode_t	mode, mode_next;
	
	always_comb begin
		case (mode)
			MODE_CRM:	length = 5'd31;
			MODE_PDCM:	length = 5'd0;
			MODE_DM:	length = 5'd3;
			default:	length = 5'd31;
		endcase
	end
	
	`include "ecc_register_inc.sv"
	`ecc_register(data, 33, 33'h1ffffffff)
	
	assign	ecc_error.double_error = data_ecc_fail;
	assign	ecc_error.single_error = data_ecc_corr;
		
	logic			dsi_out_ff;
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			mode		<= MODE_CRM;
			bit_cnt		<= '0;
			dsi_out_ff	<= 1'b1;
			dsi3_oe		<= 1'b0;
		end
		else begin
			dsi_out_ff	<= data[32];
			dsi3_oe		<= dsi3_oe_nxt;
			mode		<= mode_next;
			bit_cnt	<= bit_cnt_nxt;
		end
	end
	
	/*###   DSI3 output gating   ######################################################*/
	always_comb begin
		dsi3_oe_nxt = dsi3_oe;
		if (i_enable == 1'b0)
			dsi3_oe_nxt = 1'b0;
		else begin
			if (transmit == 1'b1)
				dsi3_oe_nxt = 1'b1;
		end
	end
	
	/*###   Wave shaping   ######################################################*/
	assign	o_tx = (dsi3_oe == 1'b1) ? dsi_out_ff : 1'b1;
	
	/*###   FSM   ######################################################*/
	typedef enum logic[2:0] {TRANSMIT_IDLE, SET_TRANSMIT_MODE, SHIFT, INVERT, WAIT_END, WAIT_HALF_A_BIT, SET_RECEIVE_MODE, TRANSMIT_RESET} transmit_state_enum; /*
	TRANSMIT_IDLE		- Nothing to do
	STARTBIT	- apply start bit
	SHIFT		- shift data
	WAIT_SHIFT	- wait with shifted data -> 4us for half bit
	INVERT		- invert bit -> manchester coding
	WAIT_END	- wait before normal level is applied
	*/
	
	logic 	o_receive_mode_enable_nxt;
	transmit_state_enum		state, state_nxt;
	transmit_time_count_t	time_cnt, time_cnt_nxt, half_bit_time_counter_value;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			state		<= TRANSMIT_IDLE;
			time_cnt	<= '0;
			o_receive_mode_enable <= 1'b0;
		end
		else begin
			state		<= state_nxt;
			o_receive_mode_enable <= o_receive_mode_enable_nxt;
			if ((tick_1us == 1'b1))
				time_cnt	<= time_cnt_nxt;				
		end
	end
	
	always_comb begin
		case (i_bit_time)
			BITTIME_8US:	half_bit_time_counter_value = 4'b0011;
			BITTIME_16US:	half_bit_time_counter_value = 4'b0111;
			BITTIME_32US:	half_bit_time_counter_value = 4'b1111;
			default: 		half_bit_time_counter_value = 4'b0011;
		endcase
	end
	
	logic	half_bit_time_over;
	assign	half_bit_time_over = ((time_cnt == half_bit_time_counter_value) && (tick_1us == 1'b1) && (state != TRANSMIT_IDLE)) ? 1'b1 : 1'b0;
	
	logic	transmit_mode_enable_time_over, transmit_mode_disable_time_over;
	assign	transmit_mode_enable_time_over	= ((time_cnt == dsi3_pkg::TRANSMIT_MODE_ENABLE_TIME	) && (tick_1us == 1'b1)) ? 1'b1 : 1'b0;
	assign	transmit_mode_disable_time_over	= ((time_cnt == dsi3_pkg::TRANSMIT_MODE_DISABLE_TIME) && (tick_1us == 1'b1)) ? 1'b1 : 1'b0;
	
	assign	start_transmission = ((i_start == 1'b1)) ? 1'b1 : 1'b0;
	
	
	// next state decoding
	always_comb begin
		state_nxt = state;
		
		bit_cnt_nxt = bit_cnt;
		time_cnt_nxt = time_cnt + 4'd1;
		mode_next = mode;
		data_next = data;
		o_pend = 1'b1;											// default: pending
		transmit = 1'b1;
		o_receive_mode_enable_nxt = 1'b1;
		o_sample_time_base = 1'b0;
		o_acknowledge_start = 1'b0;
		
		case (state) 
			TRANSMIT_IDLE: begin
				o_pend = 1'b0;
				transmit = 1'b0;
				time_cnt_nxt = '0;
				if (start_transmission == 1'b1) begin
					state_nxt = SET_TRANSMIT_MODE;
					data_next = {1'b1, i_data};					// start bit + data
					mode_next = i_mode;
					bit_cnt_nxt = '0;
					o_acknowledge_start = 1'b1;
				end
			end
			SET_TRANSMIT_MODE: begin
				o_receive_mode_enable_nxt = 1'b0;
				if (transmit_mode_enable_time_over == 1'b1) begin
					state_nxt = SHIFT;
					time_cnt_nxt = '0;				
					data_next = {1'b0, data[31:0]};
					o_sample_time_base = 1'b1;
				end
			end
			SHIFT: begin
				o_receive_mode_enable_nxt = 1'b0;
				if (half_bit_time_over == 1'b1) begin
//					state_nxt = INVERT;
					data_next = {data[31:0], 1'b1};					// Shift data
					bit_cnt_nxt = bit_cnt + 6'd1;
					time_cnt_nxt = '0;
					if ((mode == MODE_DM) && (bit_cnt == {1'b0,length}+6'd1)) begin
						state_nxt = TRANSMIT_IDLE;
					end
					else begin
						if (mode == MODE_DM) begin
							state_nxt = SHIFT;
						end
						else begin
							state_nxt = INVERT;
						end
					end
				end
			end
			INVERT: begin
				o_receive_mode_enable_nxt = 1'b0;
				if (half_bit_time_over == 1'b1) begin
					if (bit_cnt == {1'b0,length}+6'd1) begin
						if (data[32] == 1'b0) begin
							state_nxt = WAIT_HALF_A_BIT;
						end
						else begin 
							state_nxt = WAIT_END;
						end
					end
					else begin
						state_nxt = SHIFT;
					end
					data_next[32] = ~data[32];						// invert data (manchester coding)
					time_cnt_nxt = '0;
				end
			end
			WAIT_END: begin
				o_receive_mode_enable_nxt = 1'b0;
				if (half_bit_time_over == 1'b1) begin
					state_nxt = WAIT_HALF_A_BIT;
					time_cnt_nxt = '0;
					data_next = '1;
				end
			end
			WAIT_HALF_A_BIT: begin
				o_receive_mode_enable_nxt = 1'b0;
				if (half_bit_time_over == 1'b1) begin
					state_nxt = SET_RECEIVE_MODE;
					time_cnt_nxt = '0;
				end
			end
			SET_RECEIVE_MODE: begin
				o_receive_mode_enable_nxt = 1'b0;
				if (transmit_mode_disable_time_over == 1'b1) begin
					state_nxt = TRANSMIT_IDLE;
					time_cnt_nxt = '0;
				end
			end
			TRANSMIT_RESET: begin
				if (i_enable == 1'b1) begin
					state_nxt = TRANSMIT_IDLE;
				end
				o_pend = 1'b0;
				transmit = 1'b0;
				time_cnt_nxt = '0;
			end
		endcase
		if (i_enable == 1'b0) begin
			state_nxt = TRANSMIT_RESET;
		end
	end
	
endmodule


