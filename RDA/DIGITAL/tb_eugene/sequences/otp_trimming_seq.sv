class otp_trimming_seq extends base_dsi_master_seq;
    
	localparam int WAVE_SHAPE_COUNT = 72;
	
	`uvm_object_utils(otp_trimming_seq)
	
	logic[11:0] otp[4095:0];
	
	function new(string name = "");
		super.new("otp_trimming");
	endfunction : new	
   
    virtual task run_tests();

		log_sim_description("Testcase for OTP trimmings", LOG_LEVEL_TOP);
        set_sequence_interface("otp_trimming");
		$readmemh("otp_wave_shaping.dat", otp); // read OTP data from *.dat file
		
        // disable automatic check for HE flag
        get_checker_config().enable_hardware_error_check = 1'b0;
                
        check_ram_startup_value();
        #100us;
        check_otp_read_during_vcc_setup();
        #1.2ms;
        check_read_otp_by_spi();
        #100us; 
        check_unprogrammed_otp();
        #100us;
        check_otp_full_with_data();	
        #100us;
        check_otp_stop_read();
        #100us;
        check_otp_addr_ecc_err();
        #100us;
        check_otp_data_ecc_err();
        
        get_checker_config().enable_hardware_error_check = 1'b1;
        reset_sequence_interface();
    endtask
    
	virtual task power_up (time waiting=1500us);
		osc_tr osc;
		// set vcc in under voltage range for RAM test
		set_vsup(4, 20us);
		#100us;
		set_resb(1);
        
		`uvm_do_on_with (osc, m_osc_agent.m_sequencer, {enabled == 1; freq==500000;})
		#(waiting);
	endtask
	
	task check_read_otp_by_spi();
		uvm_reg_data_t    read_value;
		uvm_reg_data_t    read_status;
		int time_out = 0;
		int cnt = 0;
        
		// use the same otp_wave_shaping.dat file for the test 
		log_sim_description("Check: applicative OTP read through SPI", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check: applicative OTP read through SPI");
        
		for (int addr = 0; addr < 32; addr++) begin // 652
			regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_ADDRESS.ADDR.write(status, 12'(addr));
			while(1) begin
				regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_STATUS.STATUS.read(status, read_status);
				if(read_status == 2) 
					break;
				else cnt++;
                
				if (cnt == 50) begin
					cnt = 0;
					time_out = 1;
					`uvm_error(get_type_name(), $sformatf("OTP applicative read time out at address 0x%3h, otp read status = %2d", addr, read_status))
					break;
				end
			end
            
			regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_VALUE.VALUE.read(status, read_value);
                 
			if (time_out == 0) begin
				if(read_value != $size(read_value)'(otp[addr] & 12'h0FF))
					`uvm_error(get_type_name(), $sformatf("OTP applicative read out is not as expected at address %3h. Got %3h but expected %3h", addr, read_value, otp[addr]))
			end 
			else time_out = 0;
        end
        reset_sequence_interface();
	endtask
    
	task check_otp_full_with_data();
		log_sim_description("Check OTP full with data", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check OTP full with data");
            
		reset("otp_full.dat");
		expect_otp_fail(1'b0);
        reset_sequence_interface();
	endtask
    
	task check_unprogrammed_otp();
		log_sim_description("Check unprogrammed OTP", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check unprogrammed OTP");
            
		reset("otp_unprogrammed.dat");
		expect_otp_fail(1'b0, 1'b1);
        reset_sequence_interface();
	endtask
    
	task check_otp_read_during_vcc_setup();
		log_sim_description("Check OTP read during vcc setup", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check OTP read during vcc setup");
            
        read_otp("otp_wave_shaping.dat");   
        
		do_power_down_and_up(50us);
        reset_sequence_interface();
	endtask
    
	task do_power_down_and_up(time wait_time);
		set_clock_ref(.enable(1'b0));
		set_vsup(0, 20us);
		fork
			begin
				#10us;
				set_clock_ref(.enable(1'b1));
			end
			#(wait_time);
		join
		set_vsup(12, 20us);
	endtask
	
    
	task check_ram_startup_value();
		logic [15:0] expected_value[$];
		int index;
        
		log_sim_description("Check the startup value in RAM", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check the startup value in RAM");
            
        read_otp("otp_wave_shaping.dat");
        
		// at this moment, the RAM is still not initialized -> don't need to check the read value
		for (int ram_length=0; ram_length < int'(project_pkg::SIZE_RAM); ram_length++) begin
			check_ram(16'(project_pkg::BASE_ADDR_RAM + ram_length), ,1);
			check_rfc(1'b0);
		end
		#500us;
		// reading un-initialized RAM must not result in an ECC error
		registers.check_flag(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.RAM, 1'b0);
        
		write_something_to_ram(expected_value);
        
		for (int ram_index = int'(project_pkg::BASE_ADDR_DSI_CMD_BUF[0]); ram_index < project_pkg::BASE_ADDR_DSI_CMD_BUF[0] + expected_value.size(); ram_index++) begin
			index = ram_index - project_pkg::BASE_ADDR_DSI_CMD_BUF[0];
			check_ram(16'(project_pkg::BASE_ADDR_RAM + ram_index), expected_value[index], , "before Reset");
			check_rfc(1'b0);
		end
        
		set_resb(0);
		#10us;
		set_resb(1);
		#10us;
        
		// VCC still in under voltage range -> RAM should keep its value after reset
		for (int ram_index = int'(project_pkg::BASE_ADDR_DSI_CMD_BUF[0]); ram_index < project_pkg::BASE_ADDR_DSI_CMD_BUF[0] + expected_value.size(); ram_index++) begin
			index = ram_index - project_pkg::BASE_ADDR_DSI_CMD_BUF[0];
			check_ram(16'(project_pkg::BASE_ADDR_RAM + ram_index), expected_value[index], , "after Reset");
			check_rfc(1'b0);
		end
        
		do_power_down_and_up(200us);
		
		check_rfc(1'b0);
		wait_for_rfc();
        
		// at this moment, the OTP Read finished, RAM should be initialized -> read out value should be all zero
		for (int ram_length=0; ram_length < int'(project_pkg::SIZE_RAM); ram_length++) begin
			check_ram(16'(project_pkg::BASE_ADDR_RAM + ram_length), , ,"after RAM inizialize");
			check_rfc(1'b1);
		end
        reset_sequence_interface();
	endtask
    
	task check_ram(int target_address, int expected = 'h0000, int disable_check = 0, string info="");
		spi_read_master_register_seq read_seq;
        
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 12'd0; burst_addresses.size()==1; burst_addresses[0] == (12'(target_address) & 12'hFFF);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end   
		#1us;
        
		if (disable_check == 0) begin
			if(read_seq.data_out[3] != 16'(expected)) 
				`uvm_error(this.get_type_name(), $sformatf("unexpected value in RAM  address %04h %s, expected %04h, but was %04h", target_address, info, expected, read_seq.data_out[3]));     
		end
	endtask
    
	task write_something_to_ram(ref logic [15:0] data[$]);
		spi_crm_seq crm_seq;
        
		// Write several CRM commands indirect to DSI0_CMD_BUFFER in RAM
		`spi_frame_begin
			repeat(4) begin
				`spi_frame_send(crm_seq, channel_bits == 2'b01; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
				data.push_back(crm_seq.get_word(0));
				data.push_back(crm_seq.get_word(1));
				data.push_back(crm_seq.get_word(2));
			end
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end     
	endtask
    
	task check_otp_stop_read();
		log_sim_description("Check OTP read stop condition: address equals 0 after ECC correction", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check OTP read stop condition: address equals 0 after ECC correction");
		// 1bit error would be created in .dat file at OTP address 56:
		// replace the original data of 0x100 by 0x101, read out should be stopped here
            
        read_otp("otp_stop_read.dat");
        
		#500us;
		set_resb(0);
		#100us;
		set_resb(1);    
		#500us;
        reset_sequence_interface();
	endtask
    
	task check_otp_addr_ecc_err();
		log_sim_description("Check OTP: 2bits ECC Error in address", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check OTP: 2bits ECC Error in address");
		// 2bits error would be created in .dat file at address 32,33:
		// replace the original data of 0x8244 by 0xA246
		reset("otp_addr_ecc_err.dat");
		expect_otp_fail(1'b1);
        reset_sequence_interface();
	endtask
    
	task check_otp_data_ecc_err();
		log_sim_description("Check OTP: 2bits ECC Error in data", LOG_LEVEL_SEQUENCE);
        set_sequence_interface("Check OTP: 2bits ECC Error in data");
		// 2bits error would be created in .dat file at address 114,115:
		// replace the original data of 0x001C by 0x4018
		reset("otp_data_ecc_err.dat");
        check("Wave Shaping",  16'h0409, 114, 1'b0);
		expect_otp_fail(1'b1);
        reset_sequence_interface();
	endtask
    
	// check OTP_FAIL bit in status word and IRQ_STAT register
	task expect_otp_fail(bit expected_fail, bit expected_he_value = expected_fail );
		spi_read_status_seq status_seq;	
    	
		`spi_frame_begin
			`spi_frame_send(status_seq,)
		`spi_frame_end
		if(status_seq.status.get_value(HE) != expected_he_value) `uvm_error(this.get_name(), $sformatf("unexpected HE flag in IC status word, expected %0b, got %0b", expected_fail, status_seq.status.get_value(HE)))
    	
		registers.check_flag(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.OTPFAIL, uvm_reg_data_t'(expected_fail));
	endtask
	

    task check(string name, int target_address, int index, bit equal = 1'b1);
		int expected_value;
		spi_read_master_register_seq read_seq;
        
		// get the high byte and low byte of expected data from otp.dat file
		expected_value = int'({ 8'(otp[index] & 12'h0ff) , 8'(otp[index+1] & 12'h0ff) }); 
        
		`spi_frame_begin
			if(16'(target_address) <= 16'h0FFF) begin
				// simple read
				`spi_frame_send(read_seq, address == 12'(target_address); burst_addresses.size()==0;)
			end 
			else begin
				// use burst read to access address > 0xFFF
				`spi_frame_send(read_seq, address == 12'd0; burst_addresses.size()==1; burst_addresses[0]== (12'(target_address) & 12'hFFF);)
			end
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end  

		#1us;
        
		if (target_address < 'h0FFF) begin
			if(equal == 1'b1 && read_seq.data != 16'(expected_value)) `uvm_error(this.get_type_name(), $sformatf("unexpected value for %s, expected %04h, but was %04h", name, expected_value, read_seq.data));
			if(equal == 1'b0 && read_seq.data == 16'(expected_value)) `uvm_error(this.get_type_name(), $sformatf("unexpected value for %s, the wrong data should not be loaded in to register!", name));
		end 
		else begin
			if(equal == 1'b1 && read_seq.data_out[3] != 16'(expected_value)) `uvm_error(this.get_type_name(), $sformatf("unexpected value for %s, expected %04h, but was %04h", name, expected_value, read_seq.data_out[3])); 
			if(equal == 1'b0 && read_seq.data_out[3] == 16'(expected_value)) `uvm_error(this.get_type_name(), $sformatf("unexpected value for %s, the wrong data should not be loaded in to register!", name));
		end
	endtask
endclass
