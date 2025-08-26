/**
 * Module: dsi3_receive_sample_counter
 * 
 * Module, that samples the incoming chips, makes a majority descision up on the sampled chips and outputs the sampled chip 
 */
module dsi3_receive_sample_counter import dsi3_pkg::*; (
		clk_reset_if.slave	clk_rst,
		input	logic		i_tick_sample,
		input	logic		i_enable,
		input	logic		i_reset_counter,
		input	dsi3_chip	i_chip,
		input	dsi3_chip	i_previous_sample,
		output	dsi3_chip	o_chip
	);
	
	typedef logic [8:0]	counter_t;
	counter_t		cnt_sample[3:0], cnt_sample_nxt[3:0];	// counter for each possible value (C0, C1, C2 and CX)
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			for (int i=0; i<4; i++)
				cnt_sample[i]	<= '0;
		end
		else begin
			if (i_tick_sample == 1'b1) begin
				cnt_sample	<= cnt_sample_nxt;
			end
		end
	end	
	
	always_comb begin
		if ((i_enable == 1'b1) && (i_reset_counter == 1'b0)) begin						// when receiving is enabled
			cnt_sample_nxt = cnt_sample;			// default no change for all counters of samples
			if ((i_previous_sample == C0) && (i_chip == C2)) begin
				cnt_sample_nxt[i_chip] = cnt_sample[i_chip] + counter_t'(2);	// increment counter of incoming chip
			end
			else begin
				if ((i_previous_sample == C2) && (i_chip == C0)) begin
					cnt_sample_nxt[i_chip] = cnt_sample[i_chip] + counter_t'(2);	// increment counter of incoming chip
				end
				else begin
					cnt_sample_nxt[i_chip] = cnt_sample[i_chip] + counter_t'(1);	// increment counter of incoming chip
				end
			end
		end
		else begin
			cnt_sample_nxt = '{4{'0}};				// reset counters when starting next "frame"
		end
	end
	
	/*###   output chip generation from counter value   ######################################################*/
	logic[1:0]	_0_gt_1, _2_gt_3;
	always_comb begin
		if ((cnt_sample[0] > cnt_sample[1]) || ((cnt_sample[0] == cnt_sample[1]) && (i_previous_sample != C0)))
			_0_gt_1 = 2'd0;
		else
			_0_gt_1 = 2'd1;
	end
	
	always_comb begin
		if ((cnt_sample[2] > cnt_sample[3]) || ((cnt_sample[2] == cnt_sample[3]) && (i_previous_sample < C2)))
			_2_gt_3 = 2'd2;
		else
			_2_gt_3 = 2'd3;		
	end
	
	always_comb begin
		if ((cnt_sample[_0_gt_1] > cnt_sample[_2_gt_3]) || ((cnt_sample[_0_gt_1] == cnt_sample[_2_gt_3]) && (i_previous_sample > C1)))
			o_chip = dsi3_chip'(_0_gt_1);
		else
			o_chip = dsi3_chip'(_2_gt_3);
	end
	
endmodule


