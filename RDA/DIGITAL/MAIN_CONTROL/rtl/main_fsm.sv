/**
 * Module: main_fsm
 * 
 * main FSM for power up and OTP read out
 */
module main_fsm import	project_pkg::*; (
		clk_reset_if.slave	clk_rst,
		otp_ip_bus_if.master	otp_ip_bus,
		elip_full_if.master	elip,
		elip_if.slave		elip_registers,
		input	logic		i_vcc_ok,
		input	logic		i_vrr_ok,
		input	logic		i_ldo_ok,
		input	logic		i_ignore_ldo_uv,
		input	logic		i_ignore_hwf,
		input	logic		i_tick_1us,
		output	logic		o_enable_transceivers,
		output	logic		o_rfc,
		output	logic		o_otp_ehv,
		output	logic		o_enable_ldo,
		ecc_error_if.master	ecc_error,
		output	logic		o_main_fsm_fail,
		output	elip_data_t	o_elip_out,
		output	logic		o_initializing,
        output  logic       o_ram_initialized
	);
	
	/*###   defintions   ######################################################*/
	import	main_control_pkg::*;
	
	main_state_t state, state_next;
	
	elip_addr_t	address, address_next;
	data_ecc_t	data, data_next;
	ecc_t		ecc_for_data;
	
	otp_address_t	otp_address, otp_address_next, otp_address_applicative, otp_address_to_otp_control;
	
	logic	rfc_next;
	logic	enable_ldo_next;
	
	otp_data_structure_t	otp_data;
	logic		otp_ready, otp_read, read_applicative;
	logic		enable_otp_for_applicative_read, enable_otp_for_trimming, enable_otp;
	otp_content_t	otp_content, otp_content_next;
	otp_content_data_t	otp_content_corrected;
	
	logic	ecc_corrected, ecc_double_error;
	logic	check_ecc;
	logic	otp_content_is_unprogrammed;
	assign	otp_content_is_unprogrammed = ((otp_content.data.content == '0) && (otp_content.ecc == '0)) ? 1'b1 : 1'b0;
	
	logic	enable_applicative_otp_reading;
    
    logic   store_address, store_data;
    logic   ram_initialized_next;
	
	/*###   startup FSM   ######################################################*/
    always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
        if (clk_rst.rstn == 1'b0) begin
            state	<= RESET;
            otp_content	<= '0;
            address	<= '0;
            data.data <= '0;
            data.ecc <= ECC_FOR_DATA_0;
            o_rfc	<= 1'b0;
            otp_address	<= '0;
            o_enable_ldo <= 1'b0;
            o_ram_initialized <= 1'b0;
        end
        else begin
            state	<= state_next;
            otp_content	<= otp_content_next;
            otp_address <= otp_address_next;
            o_rfc	<= rfc_next;
            o_enable_ldo <= enable_ldo_next;
            o_ram_initialized <= ram_initialized_next;
            if (store_address == 1'b1)
                address	<= address_next;
            if (store_data == 1'b1)
                data	<= data_next;
        end
    end
	
	assign	elip.addr = address;
	assign	elip.data_write.data = data.data;
	assign  elip.data_write.ecc = data.ecc;
	
	
	`define check_abort_with_high_address if (otp_address != '0) begin \
			state_next = READ_HIGH_ADDRESS; \
		end \
		else begin \
			state_next = WAITING_AFTER_TRIMMING; \
		end \
	
	always_comb begin
		state_next = state;
		enable_otp_for_trimming = 1'b0;
		
		otp_content_next = otp_content;
		address_next = address;
		data_next = data;
		
		elip.rd = 1'b0;
		elip.wr = 1'b0;
		o_enable_transceivers = 1'b0;
		rfc_next = 1'b0;
		otp_read = 1'b0;
		
		enable_ldo_next = 1'b1;
		
		check_ecc = 1'b0;
		o_main_fsm_fail = 1'b0;
		otp_address_next = otp_address;
		
		enable_applicative_otp_reading = 1'b0;
		o_initializing = 1'b1;
		
        store_address = 1'b0;
        store_data = 1'b0;
        
        ram_initialized_next = 1'b0;
        
		case (state)
			RESET: begin
				o_initializing = 1'b0; //to be able to write IGNORE_HF 
				state_next = WAIT_FOR_VCC_OK;
                store_address = 1'b1;
				address_next = '0;
				otp_address_next = '0;
				data_next.data = '0;
				data_next.ecc  = ecc_for_data;
                store_data = 1'b1;
				enable_ldo_next = 1'b0;
			end
			WAIT_FOR_VCC_OK: begin
				o_initializing = 1'b0; //to be able to write IGNORE_HF
				enable_ldo_next = 1'b0;
				if ((i_vcc_ok == 1'b1) || (i_ignore_hwf == 1'b1)) begin
					state_next = WAIT_FOR_VRR_OK;
					enable_otp_for_trimming = 1'b1;
				end
			end
			WAIT_FOR_VRR_OK: begin
				o_initializing = 1'b0; //to be able to write IGNORE_VRR
				enable_otp_for_trimming = 1'b1;
				enable_ldo_next = 1'b0;
				if ((i_vrr_ok == 1'b1) || (i_ignore_hwf == 1'b1)) begin
					state_next = READ_HIGH_ADDRESS;
				end
			end
			READ_HIGH_ADDRESS: begin
				enable_otp_for_trimming = 1'b1;
				otp_read = 1'b1;
				otp_content_next.data.address = otp_address;
				if (otp_ready == 1'b1) begin
					state_next = READ_LOW_ADDRESS;
					otp_address_next = otp_address + 12'd1;
					otp_content_next.data.content.high = otp_data.data;
					otp_content_next.ecc.high = otp_data.ecc;
					otp_read = 1'b0;
				end
			end
			READ_LOW_ADDRESS: begin
				enable_otp_for_trimming = 1'b1;
				otp_read = 1'b1;
				if (otp_ready == 1'b1) begin
					state_next = CHECK_ADDRESS;
					otp_address_next = otp_address + 12'd1;
					otp_content_next.data.content.low = otp_data.data;
					otp_content_next.ecc.low = otp_data.ecc;
					otp_read = 1'b0;
				end
			end
			CHECK_ADDRESS: begin
				enable_otp_for_trimming = 1'b1;
				if ((otp_content_corrected.content == '0) /* corrected address is 0 */ ||
						(otp_content_is_unprogrammed == 1'b1)) /*no data at all in OTP (unprogrammed)*/
							begin // no further readout -> startup
					if (otp_content_is_unprogrammed == 1'b0) begin
						check_ecc = 1'b1;
					end
					state_next = WAITING_AFTER_TRIMMING;
					address_next = 16'(BASE_ADDR_RAM);
                    store_address = 1'b1;
					data_next.data = '0;
					data_next.ecc  = ecc_for_data;
                    store_data = 1'b1;
				end
				else begin
					address_next = otp_content_corrected.content;
                    store_address = 1'b1;
					check_ecc = 1'b1;
					if (ecc_double_error == 1'b1) begin
						state_next = READ_HIGH_ADDRESS;
						otp_address_next = otp_address + 12'd2;
					end
					else 
						state_next = READ_HIGH_DATA;
				end
			end
			
			READ_HIGH_DATA: begin
				enable_otp_for_trimming = 1'b1;
				otp_read = 1'b1;
				otp_content_next.data.address = otp_address;
				if (otp_ready == 1'b1) begin
					state_next = READ_LOW_DATA;
					otp_address_next = otp_address + 12'd1;
					otp_content_next.data.content.high = otp_data.data;
					otp_content_next.ecc.high = otp_data.ecc;
					otp_read = 1'b0;
				end
			end
			READ_LOW_DATA: begin
				enable_otp_for_trimming = 1'b1;
				otp_read = 1'b1;
				if (otp_ready == 1'b1) begin
					state_next = PREPARE_WRITE_DATA;
					otp_address_next = otp_address + 12'd1;
					otp_content_next.data.content.low = otp_data.data;
					otp_content_next.ecc.low = otp_data.ecc;
					otp_read = 1'b0;
				end
			end
			PREPARE_WRITE_DATA: begin
				check_ecc = 1'b1;
				enable_otp_for_trimming = 1'b1;
				data_next.data = otp_content_corrected.content;
				data_next.ecc  = ecc_for_data;
                store_data = 1'b1;
				if (ecc_double_error == 1'b1) begin
                    `check_abort_with_high_address
				end
				else 
					state_next = WRITE_DATA;
			end
			WRITE_DATA: begin
				enable_otp_for_trimming = 1'b1;
				elip.wr = 1'b1;
				if (elip.ready == 1'b1) begin
					`check_abort_with_high_address
				end
			end
			
			WAITING_AFTER_TRIMMING: begin
				enable_otp_for_trimming = 1'b1;
				// use otp_address for wait time
				otp_address_next = otp_address + otp_address_t'(1);
				if (!(otp_address < otp_address_t'(18*40))) begin
					state_next = RAM_ZEROING;
					address_next = elip_addr_t'(BASE_ADDR_RAM);
                    store_address = 1'b1;
					data_next.data = '0;
					data_next.ecc  = ecc_for_data;
                    store_data = 1'b1;
				end
			end
			
			RAM_ZEROING: begin
				enable_otp_for_trimming = 1'b1;
				data_next.data = '0;
				data_next.ecc  = ecc_for_data;
                store_data = 1'b1;
				elip.wr = 1'b1;
				if (elip.ready == 1'b1) begin
					if (address < elip_addr_t'(BASE_ADDR_RAM + SIZE_RAM - 16'd1)) begin
						address_next =  address + 16'd1;
                        store_address = 1'b1;
					end
					else begin
						state_next = WAIT_FOR_LDO_OK;
						address_next =  '0;
                        store_address = 1'b1;
					end
				end
			end
			
			WAIT_FOR_LDO_OK : begin
                ram_initialized_next = 1'b1;
				o_initializing = 1'b0;
				enable_otp_for_trimming = 1'b1;
				enable_applicative_otp_reading = 1'b1;
				if ((i_ldo_ok == 1'b1) || (i_ignore_ldo_uv == 1'b1)) begin
					state_next = POWERED_UP;
				end
			end
			POWERED_UP: begin
				o_initializing = 1'b0;
				enable_otp_for_trimming = 1'b1;
				o_enable_transceivers = 1'b1;
				rfc_next = 1'b1;
				enable_applicative_otp_reading = 1'b1;
                ram_initialized_next = 1'b1;
				//  stay here until reset!
			end
			default : begin
				state_next = RESET;
				o_main_fsm_fail = 1'b1;
			end
		endcase
		if ((state_next == WAITING_AFTER_TRIMMING) && (state != WAITING_AFTER_TRIMMING)) begin
			otp_address_next = otp_address_t'(0);
		end
	end
	
	/*###   ECC encoder   ######################################################*/
	ecc_encoder #(
		.DATA_WIDTH  (16 ), 
		.ECC_WIDTH   (6  )
		) i_ecc_encoder_data (
		.i_data      (data_next.data), 
		.o_ecc       (ecc_for_data  ));

	/*###   OTP control   ######################################################*/
	otp_reader i_otp_reader (
		.clk_rst         (clk_rst        ), 
		.elip_registers  (elip_registers ), 
		.i_enable        (enable_applicative_otp_reading), 
		.i_data_read     (otp_data       ), 
		.i_ready         (otp_ready      ), 
		.o_read          (read_applicative ),
		.o_enable_otp    (enable_otp_for_applicative_read),
		.o_address       (otp_address_applicative ), 
		.o_elip_out      (o_elip_out     ));
	
	/*###   OTP control   ######################################################*/
	assign	enable_otp = enable_otp_for_trimming | enable_otp_for_applicative_read;
	assign	otp_address_to_otp_control = (enable_applicative_otp_reading == 1'b1) ? otp_address_applicative : otp_address;
	
	otp_control i_otp_control (
		.clk_rst         (clk_rst                     ), 
		.otp_ip_bus      (otp_ip_bus                  ), 
		.i_enable        (enable_otp                  ), 
		.i_address       (otp_address_to_otp_control  ), 
		.i_read          (otp_read | read_applicative ), 
		.i_vcc_uv        ((i_ignore_hwf==1'b1) ? 1'b0 : ~i_vcc_ok   ), 
		.i_tick_1us      (i_tick_1us                  ), 
		.o_ehv           (o_otp_ehv                   ), 
		.o_data          (otp_data                    ), 
		.o_ready         (otp_ready                   ));
	
	/*###   OTP ECC   ######################################################*/
	ecc_decoder #(
			.DATA_WIDTH   (OTP_CONTENT_DATA_WIDTH  ), 
			.ECC_WIDTH    (8   )
		) ecc_decoder (
			.i_correct_n  (1'b0 ), 
			.i_data       (otp_content.data   ), 
			.i_ecc        (otp_content.ecc    ), 
			.o_data       (otp_content_corrected), 
			.o_ecc_cor    (ecc_corrected   ), 
			.o_ecc_err    (ecc_double_error   ));
	
	assign	ecc_error.double_error = ecc_double_error & check_ecc;
	assign	ecc_error.single_error = ecc_corrected & check_ecc;
	
endmodule
