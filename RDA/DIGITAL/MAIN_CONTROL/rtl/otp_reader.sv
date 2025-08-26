/**
 * Module: otp_reader
 * 
 * module for applicative OTP readout
 */
module otp_reader import project_pkg::*; import main_control_pkg::*; (
		clk_reset_if.slave	clk_rst,
		elip_if.slave		elip_registers,
		input 	logic		i_enable,
		input	otp_data_structure_t	i_data_read,
		input	logic		i_ready,
		output	logic		o_read,
		
		output	logic		o_enable_otp,
		
		output	otp_address_t	o_address,
		output	elip_data_t	o_elip_out
	);
	
	`include "OTP_readout_register_if_inst.sv"
	
	typedef	enum logic {IDLE, OTP_READING}	otp_reader_state_t;
	otp_reader_state_t	state, state_next;
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			state	<= IDLE;
		end
		else begin
			state	<= state_next;
		end
	end
	
	assign	OTP_readout_register_OTP_READ_VALUE.VALUE_in = i_data_read.data;
	assign	OTP_readout_register_OTP_READ_VALUE.ECC_in = i_data_read.ecc;
	
	`define set_status(_status_)	OTP_readout_register_OTP_READ_STATUS.STATUS_in = _status_; \
		OTP_readout_register_OTP_READ_STATUS.STATUS_set = 1'b1;
	
	always_comb begin
		OTP_readout_register_OTP_READ_VALUE.VALUE_set = 1'b0;
		OTP_readout_register_OTP_READ_VALUE.ECC_set = 1'b0;
		OTP_readout_register_OTP_READ_STATUS.STATUS_in = '0;
		OTP_readout_register_OTP_READ_STATUS.STATUS_set = 1'b0;
		o_enable_otp = 1'b0;
		state_next = state;
		o_read = 1'b0;
		case (state)
			IDLE: begin
				if (OTP_readout_register_OTP_READ_ADDRESS.access_wr == 1'b1) begin
					if (i_enable == 1'b1) begin
						state_next = OTP_READING;
						`set_status(main_control_pkg::READING)
						o_enable_otp  = 1'b1;
					end
					else begin
						`set_status(main_control_pkg::FAIL)
					end
				end
			end
			OTP_READING: begin
				o_read = 1'b1;
				o_enable_otp = 1'b1;
				if (i_ready == 1'b1) begin
					o_read = 1'b0;
					state_next = IDLE;
					OTP_readout_register_OTP_READ_VALUE.ECC_set = 1'b1;
					OTP_readout_register_OTP_READ_VALUE.VALUE_set = 1'b1;
					`set_status(main_control_pkg::FINISHED)
				end
			end
		endcase
	end
	
	
	
	OTP_readout_register #(
		.base_addr                              (0                                            ), 
		.addr_width                             (ELIP_ADDR_WIDTH                              )
		) i_OTP_readout_register (
		.clk_rst                                (clk_rst                                      ), 
		.addr                                   (elip_registers.addr                          ), 
		.data_in                                (elip_registers.data_write                    ), 
		.wr                                     (elip_registers.wr                            ), 
		.rd                                     (elip_registers.rd                            ), 
		.data_out                               (o_elip_out                                   ), 
		.OTP_readout_register_OTP_READ_ADDRESS  (OTP_readout_register_OTP_READ_ADDRESS.master ), 
		.OTP_readout_register_OTP_READ_VALUE    (OTP_readout_register_OTP_READ_VALUE.master   ), 
		.OTP_readout_register_OTP_READ_STATUS   (OTP_readout_register_OTP_READ_STATUS.master  ));
	
	assign	o_address = OTP_readout_register_OTP_READ_ADDRESS.ADDR;
	

endmodule


