/**
 * Module: clock_auto_trimming
 * 
 * module for auto trimming of internal oscillator
 */
module clock_auto_trimming(
		clk_reset_if.slave	clk_rst,
		time_base_registers_TRIM_OSC_if.slave time_base_registers_TRIM_OSC,
		
		input	logic	i_auto_trim_enable,
		input	logic	i_clkref_rising
	);
	
	logic[8:0]	cnt, cnt_nxt;
	logic[3:0]	counter_increment, counter_increment_nxt;
	logic		auto_trim_en, auto_trim_finished, counted_upwards, counted_upwards_nxt;
	logic		start_auto_trimming;
	
	typedef enum logic[1:0] {IDLE, START_TRIMMING, TRIMMING, STOPPED} auto_trimming_state;
	auto_trimming_state		trim_state, trim_state_nxt;
	
	/*###   FFs   ######################################################*/
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt		<= '0;
			counter_increment	<= 4'hf;
			counted_upwards <= 1'b1;
			trim_state	<= IDLE;
		end
		else begin
			trim_state <= trim_state_nxt;
			if (auto_trim_en == 1'b1) begin
				cnt <= cnt_nxt;
				counter_increment <= counter_increment_nxt;
				counted_upwards	<= counted_upwards_nxt;
			end
		end
	end
	
	assign	start_auto_trimming = i_auto_trim_enable & i_clkref_rising;
	
	/*###   counter   ######################################################*/
	always_comb begin
		cnt_nxt = cnt;
		if (cnt != '1) begin
			cnt_nxt = cnt + 9'd1;
		end
		if (auto_trim_en == 1'b1) begin
			if (i_clkref_rising == 1'b1) begin
				cnt_nxt = '0;
			end
			if (auto_trim_finished == 1'b1) begin
				cnt_nxt = '0;
			end
		end
	end
	
	always_comb begin
		auto_trim_finished = 1'b0;
		if (trim_state == TRIMMING) begin
			if (i_clkref_rising == 1'b1) begin
				if (cnt == 9'h0ff) begin
					if (counter_increment == 4'h1) begin
						auto_trim_finished = 1'b1;
					end
				end
			end
		end
	end
	
	/*###   FSM states   ######################################################*/
	always_comb begin
		trim_state_nxt = trim_state;
		case (trim_state)
			IDLE: begin
				if (start_auto_trimming == 1'b1) begin
					trim_state_nxt = START_TRIMMING;
				end
			end
			START_TRIMMING: begin
				trim_state_nxt = TRIMMING;
			end
			TRIMMING: begin
				if (auto_trim_finished == 1'b1) begin
					trim_state_nxt = STOPPED;
				end
			end
			STOPPED: begin
				if (i_auto_trim_enable == 1'b0) begin
					trim_state_nxt = IDLE;
				end
			end
		endcase
	end
	
	always_comb begin
		time_base_registers_TRIM_OSC.TRIM_OSC_set = 1'b0;
		time_base_registers_TRIM_OSC.TRIM_OSC_in = time_base_registers_TRIM_OSC.TRIM_OSC;
		counter_increment_nxt = counter_increment;
		counted_upwards_nxt = counted_upwards;
		auto_trim_en = 1'b0;
		case (trim_state)
			IDLE: begin
				
			end
			START_TRIMMING: begin
				auto_trim_en = 1'b1;
				counter_increment_nxt	= 4'hf;
				counted_upwards_nxt		= 1'b1;
				time_base_registers_TRIM_OSC.TRIM_OSC_set = 1'b1;
				time_base_registers_TRIM_OSC.TRIM_OSC_in = '0;
			end
			TRIMMING: begin
				auto_trim_en = 1'b1;
				if (i_clkref_rising == 1'b1) begin
					time_base_registers_TRIM_OSC.TRIM_OSC_set = 1'b1;
					if (cnt > 9'h0ff) begin
						if (!(time_base_registers_TRIM_OSC.TRIM_OSC < 7'(counter_increment))) begin
							time_base_registers_TRIM_OSC.TRIM_OSC_in = time_base_registers_TRIM_OSC.TRIM_OSC - 7'(counter_increment);
						end
						else begin
							time_base_registers_TRIM_OSC.TRIM_OSC_in = '0;
						end
						counted_upwards_nxt = 1'b0;
						if (counted_upwards == 1'b1) begin
							if (counter_increment > 4'h1) begin
								counter_increment_nxt = counter_increment >> 1;
							end
						end
					end
					else begin
						if (cnt < 9'h0ff) begin
							if (!(time_base_registers_TRIM_OSC.TRIM_OSC > (7'h7f-7'(counter_increment)))) begin
								time_base_registers_TRIM_OSC.TRIM_OSC_in = time_base_registers_TRIM_OSC.TRIM_OSC + 7'(counter_increment);
							end
							else begin
								time_base_registers_TRIM_OSC.TRIM_OSC_in = '1;
							end
							counted_upwards_nxt = 1'b1;
							if (counted_upwards == 1'b0) begin
								if (counter_increment > 4'h1) begin
									counter_increment_nxt = counter_increment >> 1;
								end
							end
						end
					end
				end
			end
			STOPPED: begin
				counter_increment_nxt	= 4'hf;
				counted_upwards_nxt		= 1'b1;
			end
		endcase
	end


endmodule


