/**
 * Module: dsi3_start_tick_generator
 * 
 * generates tick for starting channels in a time schedule defined by a shift register
 * tick generation in PDCM is also dependent whether the PDCM pulses shall come synchronized or not
 */
module dsi3_start_tick_generator import project_pkg::*; (
		clk_reset_if.slave				clk_rst,
		dsi3_common_config_if.slave		common_config,
		dsi3_start_request_if.slave		request[DSI_CHANNELS-1:0],
		input	dsi_logic_t				gate_pdcm
	);
	
	import dsi3_pkg::*;
	
	dsi_logic_t	tick_transmit, tick_pdcm;
	
	logic		any_transmit_ongoing, any_pdcm_in_progress;
	dsi_logic_t	transmit_in_progress_at_channel, pdcm_in_progress_at_channel;
	dsi_logic_t	pdcm_receive_timeout;
	dsi_logic_t	period_running, start_period_counter, stop_period_counter;
	logic		request_transmit_ticks, request_transmit_ticks_next;
	logic		start_pdcms, start_pdcms_next;
	dsi_logic_t	request_tick, request_pdcm, request_pdcm_next;
	
	assign	any_transmit_ongoing = |(transmit_in_progress_at_channel);
	assign	any_pdcm_in_progress = |(pdcm_in_progress_at_channel);
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			start_pdcms	<= 1'b0;
			request_transmit_ticks <= 1'b0;
			request_pdcm <= '0;
		end
		else begin
			start_pdcms	<= start_pdcms_next;
			request_transmit_ticks <= request_transmit_ticks_next;
			request_pdcm <= request_pdcm_next;
		end
	end
	
	generate
		genvar channel;
		for (channel=0; channel<DSI_CHANNELS; channel++) begin : generate_start_modules
			assign	transmit_in_progress_at_channel[channel]	= request[channel].transmitting;
			assign	request_tick[channel] = request[channel].request;
			assign	request_pdcm_next[channel] = (request[channel].mode == MODE_PDCM) ? request[channel].request : 1'b0;
			
			assign	request[channel].tick_transmit = tick_transmit[channel];
			assign	request[channel].tick_pdcm = tick_pdcm[channel];
			
			assign	request[channel].pdcm_period_running = period_running[channel];
			assign	request[channel].pdcm_receive_timeout = pdcm_receive_timeout[channel];
			assign	pdcm_in_progress_at_channel[channel] = request[channel].pdcm_in_progress;
		end
	endgenerate
	
	always_comb begin
		start_pdcms_next = start_pdcms;
		if (common_config.sync_pdcm == 1'b1) begin
			if ((any_pdcm_in_progress == 1'b0) && (start_pdcms == 1'b0)) begin
				start_pdcms_next = |(request_pdcm_next &(~gate_pdcm) );
			end
			else begin
				if (tick_transmit[DSI_CHANNELS-1] == 1'b1) begin
					start_pdcms_next = 1'b0;
				end
			end
		end
	end
	
	always_comb begin
		if (common_config.sync_pdcm == 1'b1) begin
			// all period counters must run if one channel is running in PDCM (-> for generating corresponding tick_pdcm. e.g. channel 3 is running and channel 1 wants to start.)
			// shift is done initially with transmit_tick
			// first start is done with request
			// first request will start period counter of channel 0
			// transmission starts with tick transmit of corresponding channel
			// if a channel wants to start while one other is already running -> start with it's tick_pdcm from period counter
			if ((start_pdcms == 1'b1) || (start_pdcms_next == 1'b1)) begin
				start_period_counter = (tick_transmit & ~period_running);
			end
			else begin
				if (any_pdcm_in_progress == 1'b1) begin
					start_period_counter = ~period_running;
				end
				else begin
					start_period_counter = '0;
				end
			end
		end
		
		else begin
			// first start with tick transmit if requested and then when channel is currently running start with ~o_running
			for (int i=0; i<DSI_CHANNELS; i++) begin
				if (pdcm_in_progress_at_channel[i] == 1'b1) begin
					start_period_counter[i] = ~period_running[i];
				end
				else begin
					start_period_counter[i] = tick_transmit[i] & request_pdcm[i];
				end
			end
		end
	end

	assign	tick_pdcm = start_period_counter;
	
	// global stop in sync_pdcm when no PDCM is running anymore and no new request is present
	always_comb begin
		stop_period_counter = '0;
		if (common_config.sync_pdcm == 1'b1) begin
			if ((any_pdcm_in_progress == 1'b0) && (request_pdcm == '0)) begin
				stop_period_counter = '1;
			end
		end
	end
	
	always_comb begin
		request_transmit_ticks_next = request_transmit_ticks;
		if (request_transmit_ticks == 1'b0) begin
			if (request_tick != '0) begin
				request_transmit_ticks_next = 1'b1;
			end
		end
		else begin
			if ((any_pdcm_in_progress == 1'b0) && (any_transmit_ongoing == 1'b0) && (request_tick == '0)) begin
				request_transmit_ticks_next = 1'b0;
			end
		end
	end
	
	generate
		genvar	k;
		for (k = 0; k < DSI_CHANNELS; k++) begin : generate_period_counter
			period_counter i_period_counter (
					.clk_rst             (clk_rst              ), 
					.i_new_period_value  (request[k].pdcm_period), 
					.i_start             (start_period_counter[k] ),
					.i_stop              (stop_period_counter[k]  ),
					.o_receive_timeout   (pdcm_receive_timeout[k] ),
					.o_running           (period_running[k]       ));
			
		end
	endgenerate
	
	txshift_controller i_txshift_controller (
			.clk_rst                 (clk_rst                ),
			.common_config           (common_config          ), 
			.i_run                   (request_transmit_ticks ), 
			.o_tick                  (tick_transmit          ));
	
endmodule


