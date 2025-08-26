/**
 * Module: synchronization_manager_block
 * 
 * module for synchronisation of one DSI3 channel
 */
module synchronization_manager_block import project_pkg::*; import dsi3_pkg::*;(
		clk_reset_if.slave	clk_rst,
		synchronization_if.slave	sync,
		input	channel_selector_t	i_channels_to_synchronize[DSI_CHANNELS-1:0],
		input	logic				i_register_sync,
		input	logic				i_external_sync,
		output	channel_selector_t	o_channels_to_synchronize,
		output	logic				o_sync_error
	);
	
	typedef enum logic	{SYNC_IDLE, ARMED} state_t;
	state_t		state, state_next;
	
	channel_selector_t	sync_register, sync_register_next;
	channel_selector_t	fire;
	
	logic	decrement_sync_command_counter;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			state	<= SYNC_IDLE;
			sync_register	<= '0;
		end
		else begin
			state	<= state_next;
			sync_register	<= sync_register_next;
		end
	end
	
	assign	o_channels_to_synchronize = (sync.waiting == 1'b1) ? sync_register : '0;
	assign	sync.currently_registered_channels = sync_register;
	
	generate
		genvar i;
		for (i=0; i< DSI_CHANNELS; i++) begin : generate_fire_conditions
			always_comb begin
				if (sync_register[i] == 1'b1) begin
					if (sync_register == i_channels_to_synchronize[i]) begin
						fire[i] = 1'b1;
					end
					else begin
						fire[i] = 1'b0;
					end
				end
				else begin
					fire[i] = 1'b1;
				end
			end
		end
	endgenerate
	
	always_comb begin
		if (sync_register[DSI_CHANNELS] == 1'b1) begin
			fire[DSI_CHANNELS] = i_external_sync;
		end
		else begin
			fire[DSI_CHANNELS] = 1'b1;
		end
	end
	
	always_comb begin
		state_next = state;
		sync_register_next = sync_register;
		
		sync.armed = 1'b0;
		sync.fire = 1'b0;
		
		decrement_sync_command_counter = 1'b0;
		
		case (state)
			SYNC_IDLE: begin
				if(sync.register == 1'b1) begin
					sync_register_next = sync.channels_to_sync;
					state_next = ARMED;
				end
			end
			ARMED: begin
				sync.armed = 1'b1;
				if (fire == '1) begin
					state_next = SYNC_IDLE;
					sync.fire = 1'b1;
					sync_register_next = '0;
					decrement_sync_command_counter = 1'b1;
				end
			end
			default: begin
				state_next = SYNC_IDLE;
				sync_register_next = '0;
			end
		endcase
		if (sync.reset == 1'b1) begin
			state_next = SYNC_IDLE;
			sync_register_next = '0;
		end
		
	end
	
	/*###   counter for sync error   ######################################################*/
	typedef logic[7:0]	sync_command_counter_t;
	sync_command_counter_t	sync_command_counter, sync_command_counter_next;
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			sync_command_counter	<= '0;
		end
		else begin
			sync_command_counter	<= sync_command_counter_next;
		end
	end
	
	logic	increment, decrement;
	assign	increment = i_register_sync & (~decrement_sync_command_counter);
	assign	decrement = decrement_sync_command_counter & (~i_register_sync);
	
	always_comb begin
		if (increment == 1'b1) begin
			if (sync_command_counter != '1) begin
				sync_command_counter_next = sync_command_counter + sync_command_counter_t'(1);
			end
			else sync_command_counter_next = sync_command_counter;
		end
		else begin
			if (decrement == 1'b1) begin
				if (sync_command_counter != '0) begin
					sync_command_counter_next = sync_command_counter - sync_command_counter_t'(1);
				end
				else sync_command_counter_next = sync_command_counter;
			end
			else sync_command_counter_next = sync_command_counter;
		end
		if (sync.reset == 1'b1) begin
			sync_command_counter_next = '0;
		end
	end
	
	always_comb begin
		o_sync_error = 1'b0;
		if (sync.reset == 1'b1) begin
			if (sync_command_counter != '0) begin
				o_sync_error = 1'b1;
			end
		end
	end
	
	

endmodule


