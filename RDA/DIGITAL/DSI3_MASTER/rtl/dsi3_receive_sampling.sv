/**
 * Module: dsi3_receive_sampling
 * 
 * Sampling of the incoming chips
 * 
 */
module dsi3_receive_sampling  import dsi3_pkg::*; (
		clk_reset_if.slave	clk_rst,
		input	logic		i_enable,				// enable ???
		input	logic[1:0]	i_sample_cfg,			// configuration of used samples
		input	logic		i_stop_receiving,		// flag to stop receiving and wait for new data
		dsi3_chip_if.slave	chip_in,				// input chip (to be sampled)
		dsi3_chip_if.master chip_out,				// (over-)sampled chip
		output	logic		o_chip_ready,			// new chip available
		output	logic		o_receiving,			// receiving data
		output	logic		o_rec_start_tick		// receiving started when this tick is '1'
	);
	
	typedef enum logic[1:0]	{RECEIVE_IDLE, RECEIVE_FIRST_CHIP, RECEIVE} state_t;
	state_t			state, state_next;
	
	logic [7:0]		count_sample_ticks;				// counter to count the sample ticks
	dsi3_chip		chip_prev;						// save previous chip (for edge detections)
	dsi3_chip		sample_prev, sample_prev_nxt;	// save previous sample (for sample decision)
	
	logic			chip_change;					// a change between incoming chip and previous chip is detected
	
	assign	chip_change = (chip_prev != chip_in.chip) ? 1'b1 : 1'b0;
	
	logic[2:0] chip_time;
	always_comb begin
		chip_time = 3'd2 + {1'b0, i_sample_cfg};
	end
	
	logic [6:0]	max_samples;						// maximum number of samples
	assign		max_samples = 7'(chip_time) * 7'd18;	// configure number of samples
	
	logic [5:0]		sample_uncertainty;				// number of sample ticks after a new period or before a new period in which a change of chip may occur
	always_comb begin
		sample_uncertainty = 6'(chip_time)*6'd6;		// simplified calculation
	end
	
	logic			chip_ready_nxt;
	logic			receiving_next;
	logic			receiving_started_tick_next;
	
	/*###   enabling of receiving   ######################################################*/
	/* enable receiving when
	 * - an edge is incoming (chip != C0) (every symbol start with a chip != C0, from DSI3 standard)
	 */
	logic	receiving_enabled, receiving_enabled_nxt;
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			receiving_enabled	<= 1'b0;
			state				<= RECEIVE_IDLE;
			o_receiving			<= 1'b0;
			o_rec_start_tick	<= 1'b0;
		end
		else begin
			receiving_enabled<= receiving_enabled_nxt;
			state				<= state_next;
			o_receiving			<= receiving_next;
			o_rec_start_tick	<= receiving_started_tick_next;
		end
	end
	/*###   counters   ######################################################*/
	logic		edge_too_late, edge_too_early;
	logic		counter_reset_for_edge_too_late, counter_reset_for_edge_too_late_nxt;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			counter_reset_for_edge_too_late <= 1'b0;
		end
		else begin
			counter_reset_for_edge_too_late <= counter_reset_for_edge_too_late_nxt;
		end
	end	
	
	logic	new_sample_cycle;
	always_comb begin
		edge_too_early = 1'b0;
		edge_too_late  = 1'b0;
		if(receiving_enabled == 1'b1) begin
			counter_reset_for_edge_too_late_nxt = counter_reset_for_edge_too_late;
			if ((count_sample_ticks < {2'b00, sample_uncertainty}) && (chip_change == 1'b1) && (counter_reset_for_edge_too_late == 1'b0)) begin
				edge_too_late  = 1'b1;
				counter_reset_for_edge_too_late_nxt = 1'b1;
			end
			if ((count_sample_ticks >= (8'(max_samples) - 8'(sample_uncertainty) - 8'd1)) && (chip_change == 1'b1)) begin
				edge_too_early  = 1'b1;
				counter_reset_for_edge_too_late_nxt = 1'b0;
			end
			if (new_sample_cycle == 1'b1)
				counter_reset_for_edge_too_late_nxt = 1'b0;
		end else
			counter_reset_for_edge_too_late_nxt = 1'b1;
	end
	
	always_comb begin
		new_sample_cycle = 1'b0;
		if (receiving_enabled == 1'b1) begin
			if (edge_too_early == 1'b1)
				new_sample_cycle = 1'b1;
			if (count_sample_ticks == (8'(max_samples) - 8'd1))
				new_sample_cycle = 1'b1;
		end
	end
	
	logic	reset_sample_counter;
	dsi3_receive_counter i_dsi3_receive_counter (
		.clk_rst    (clk_rst             ), 
		.i_count    (1'b1                ),
		.i_enable   (receiving_enabled   ),
		.i_restart  (reset_sample_counter), 
		.o_cnt      (count_sample_ticks  )
	);

	dsi3_pkg::dsi3_chip	new_chip;
	dsi3_receive_sample_counter i_dsi3_receive_sample_counter (
		.clk_rst        (clk_rst       ), 
		.i_tick_sample  (1'b1 ), 
		.i_enable       (receiving_enabled), 
		.i_reset_counter(reset_sample_counter),
		.i_chip         (chip_in.chip  ),
		.i_previous_sample (sample_prev),
		.o_chip         (new_chip      )
	);
	
	always_comb begin
		reset_sample_counter = 1'b0;
		if ((new_sample_cycle == 1'b1) || (edge_too_late == 1'b1) || ~receiving_enabled)
			reset_sample_counter = 1'b1;
	end
	
	dsi3_chip	chip_sampled, chip_sampled_nxt;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			chip_prev			<= C0;
			chip_sampled		<= C0;
			sample_prev			<= C0;
			o_chip_ready		<= 1'b0;
		end
		else begin
			chip_prev 			<= chip_in.chip;			// save previous chip
			chip_sampled		<= chip_sampled_nxt;
			//TODO: check chip used for the counter(s) and chip saved are equal
			sample_prev			<= sample_prev_nxt;
			o_chip_ready		<= chip_ready_nxt;
		end
	end
	
	always_comb begin
		state_next = state;
		receiving_started_tick_next = 1'b0;
		chip_ready_nxt = 1'b0;
		chip_sampled_nxt 	= chip_sampled;			// save value
		receiving_enabled_nxt = receiving_enabled;
		sample_prev_nxt = sample_prev;
		receiving_next = 1'b0;
		
		case (state)
			RECEIVE_IDLE: begin
				receiving_enabled_nxt = 1'b0;
				//start when chip_in is unequal C0 and CX independet from chip_prev! P52143-576
				// (otherwise, timing error not possible for tooooo early packets or toooooo late packets in PDCM) 
				if ((i_enable == 1'b1) && ((chip_in.chip != C0) && (chip_in.chip != CX))) begin // && (chip_prev == C0))) begin 
					receiving_enabled_nxt = 1'b1;
					state_next = RECEIVE_FIRST_CHIP;
					receiving_started_tick_next = 1'b1;
				end
				else begin
					sample_prev_nxt = C0;
				end
			end
			RECEIVE_FIRST_CHIP: begin
				if ((i_stop_receiving == 1'b1) || (i_enable == 1'b0) ) begin
					state_next = RECEIVE_IDLE;
				end
				else begin
					if (new_sample_cycle == 1'b1) begin
						if (new_chip == C0) begin
							state_next = RECEIVE_IDLE;
							receiving_enabled_nxt = 1'b0;
						end
						else begin
							chip_ready_nxt = 1'b1;
							chip_sampled_nxt = new_chip;			// next sample from counters
							sample_prev_nxt = new_chip;
							state_next = RECEIVE;
							receiving_next = 1'b1;
						end
					end
				end
			end
			RECEIVE:  begin
				receiving_next = 1'b1;
				if ((i_stop_receiving == 1'b1) || (i_enable == 1'b0) ) begin
					state_next = RECEIVE_IDLE;
					receiving_next = 1'b0;
				end
				if (new_sample_cycle == 1'b1) begin
					chip_ready_nxt = 1'b1;
					chip_sampled_nxt = new_chip;			// next sample from counters
					sample_prev_nxt = new_chip;
				end
			end
			default: begin
				state_next = RECEIVE_IDLE;
			end
		endcase
	end
	
	assign	chip_out.chip = chip_sampled;
	
endmodule
