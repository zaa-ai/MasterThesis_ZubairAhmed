/**
 * Module: otp_ctrl
 * 
 * Module to access OTP via ELIP
 */
module otp_control import main_control_pkg::*;(
		clk_reset_if.slave		clk_rst,
		otp_ip_bus_if.master	otp_ip_bus,
		input	logic			i_enable,
		input	otp_address_t	i_address,
		input	logic			i_read,
		input	logic			i_vcc_uv,
		input	logic			i_tick_1us,
		output	logic			o_ehv,
		output	otp_data_t		o_data,
		output	logic			o_ready
	);
	
	typedef enum logic[1:0] {IDLE, WAIT_FOR_ACKNOWLEDGE, READ} otp_fsm_state;
	
	otp_fsm_state	state, state_nxt;
	logic	read_request, read_request_nxt;
	logic	ehv_nxt;
	logic[2:0]	cnt_ehv, cnt_ehv_nxt;
	logic	env_timing_ready;
	
	logic	set_data, set_address;
	logic	ready, ready_next;
	otp_data_t		data;
	otp_address_t	address;
	
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			state			<= IDLE;
			read_request	<= 1'b0;
			cnt_ehv			<= '0;
			o_ehv			<= 1'b0;
			data			<= '0;
			address			<= '0;
			ready			<= '0;
		end
		else begin
			state			<= state_nxt;
			read_request	<= read_request_nxt;
			cnt_ehv			<= cnt_ehv_nxt;
			o_ehv			<= ehv_nxt;
			ready			<= ready_next;
			if (set_data) begin
				data		<= otp_ip_bus.data;
			end
			if (set_address) begin
				address		<= i_address;
			end
		end
	end
	
	//TODO: check what has to be done when VCC goes low while reading -> reread?
	
	logic	goto_read;
	assign	goto_read = ((i_read == 1'b1) && (i_vcc_uv == 1'b0) && (env_timing_ready == 1'b1)) ? 1'b1 : 1'b0;
	
	assign	otp_ip_bus.read_mode = 2'd0; //not redundant nor differential mode
	assign	otp_ip_bus.addr = address;
	assign	otp_ip_bus.sel = 2'b0;
	assign	otp_ip_bus.we = 1'b0;
	
	always_comb begin
		state_nxt = state;

		otp_ip_bus.stb = 1'b0;
		
		
		set_data = 1'b0;
		set_address = 1'b0;
		
		if (i_read == 1'b1) begin
			read_request_nxt = 1'b1;
		end
		else begin
			read_request_nxt = read_request;
		end
		
		ready_next = ready & i_read;
		
		case (state)
			IDLE: begin
				if (goto_read == 1'b1) begin
					state_nxt = WAIT_FOR_ACKNOWLEDGE;
					ready_next = 1'b0;
					set_address = 1'b1;// do not allow ADDR change when reading!
				end
			end
			WAIT_FOR_ACKNOWLEDGE: begin
				otp_ip_bus.stb = 1'b1;
				if (otp_ip_bus.ack == 1'b0) begin
					state_nxt = READ;
				end
				else begin
					read_request_nxt = 1'b0;
					state_nxt = IDLE;
					set_data = 1'b1;
					ready_next = 1'b1;
				end
			end
			READ: begin
				otp_ip_bus.stb = 1'b1;
				if (otp_ip_bus.ack == 1'b1 & i_vcc_uv == 1'b0) begin
					read_request_nxt = 1'b0;
					state_nxt = IDLE;
					set_data = 1'b1;
					ready_next = 1'b1;
				end
				if (i_vcc_uv == 1'b1) begin
					read_request_nxt = 1'b1;
					state_nxt = READ;
				end
				
			end
			default: begin
				state_nxt = IDLE;
			end
		endcase
	end
	
	assign	o_ready = ready; // & ~goto_read & ~i_read;
	assign	o_data = data;
	
	assign	otp_ip_bus.sleep = ~i_enable | i_vcc_uv;
	
	/*###   EHV timing   ######################################################*/
	assign	ehv_nxt = i_enable;
	
	always_comb begin
		cnt_ehv_nxt = '0;
		if ((i_enable == 1'b1) && (i_vcc_uv == 1'b0)) begin
			if ((cnt_ehv != '1) && (i_tick_1us == 1'b1)) begin
				cnt_ehv_nxt = cnt_ehv + 3'd1;
			end
			else begin
				cnt_ehv_nxt = cnt_ehv;
			end
		end
	end
	
	assign	env_timing_ready = (cnt_ehv == '1) ? 1'b1 : 1'b0;
	
endmodule



