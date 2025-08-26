class otp_applicative_readout_fail_by_vcc_while_reading_seq extends base_otp_seq;

	`uvm_object_utils(otp_applicative_readout_fail_by_vcc_while_reading_seq)
	
	function new(string name = "");
		super.new("otp_applicative_readout_fail_by_vcc_while_reading");
	endfunction : new
	
	virtual task run_tests();
		string file_name = "otp_appl_readout_vcc_vrr_fail.dat";
		trimming trimmings[$];
		logic[7:0] otp_content[$];
		int index=0;
		otp_read_status_t status = BUSY;
		
		log_sim_description("applicative OTP readout fails when VCC goes to NOK while readout", LOG_LEVEL_SEQUENCE);
		
        get_checker_config().enable_hardware_error_check = 1'b0;
        
		`ifdef GATE_LEVEL
			`uvm_info(get_type_name(), "skipped sequence, this sequence cannot be executed at gate level", UVM_MEDIUM)
			return;
		`endif
		
		init_trimmings(trimmings);
		write_trimmings(trimmings, file_name);
		reset(file_name);
		
		while (trimmings.size > 0) begin
			trimming current_trimming;
			logic[15:0] address, data;
			current_trimming = trimmings.pop_front();
			address = 16'(current_trimming.register.get_address());
			data = current_trimming.data;
			otp_content.push_back(address[15:8]);
			otp_content.push_back(address[ 7:0]);
			otp_content.push_back(data[15:8]);
			otp_content.push_back(data[ 7:0]);
		end
		registers.check_register(regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_STATUS, 0);
		
		for (int delay = 0; delay < 2000; delay+=50) begin
			otp_read_status_t	current_status;
			log_sim_description($sformatf("applicative OTP readout fails when VCC goes to NOK while readout with delay=%1dns", delay), LOG_LEVEL_OTHERS);
			wait_for_1us_tick();
//			#4.00us; //FIXME: dependent on SPI speed : in 521.43 SPI command took 2.5us + 0.3us execution, in 521.44 SPI command is 3.7us with 1 word CSB handler
			registers.write_and_check_register(regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_ADDRESS, index);
			fork
				begin
					get_OTP_READ_STATUS(current_status);
				end
				begin
                    #0.1us;
					#(delay*1ns);
					set_vcc_uv(1'b1);
					#1us;
				end
			join
			
			if (current_status != BUSY) begin
				if (current_status == READY) begin
					if (status != READY) status = READY;
				end
				else
					if (!((delay == 0) && (current_status == INITIAL))) 
						`uvm_error(this.get_type_name(), $sformatf("unexpected OTP read status! Got %s", current_status.name()))
			end
			else begin
				if (current_status != status) `uvm_error(this.get_type_name(), $sformatf("Unallowed change of status in test case. Previous status was %s while current status is %s", status.name(), current_status.name()))
				if (delay > 800) `uvm_error(this.get_type_name(), $sformatf("Shifting of VCC UV is too large"))
			end
			set_vcc_uv(1'b0);
			#200us;
			check_trimming(index, otp_content[index], READY);
			
			if (index >= otp_content.size()) index=0; else index++;
        end
        
        get_checker_config().enable_hardware_error_check = 1'b1;
	endtask
endclass