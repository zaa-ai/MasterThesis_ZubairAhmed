class otp_applicative_readout_seq extends base_otp_seq;

	`uvm_object_utils(otp_applicative_readout_seq)
	
	function new(string name = "");
		super.new("otp_applicative_readout");
	endfunction : new
	
	virtual task run_tests();
		string file_name = "otp_appl_readout.dat";
		ecc_otp_writer otp_writer = new();
		address_data_otp_entry entries[$];
		
		log_sim_description("applicative OTP readout with single/double/none ECC failures", LOG_LEVEL_SEQUENCE);
				
		for (int i = 0; i < 4096/4; i++) begin
			address_data_otp_entry e = new();
			if(!e.randomize() with {address inside {[int'(project_pkg::BASE_ADDR_RAM) : int'(project_pkg::BASE_ADDR_RAM + project_pkg::SIZE_RAM - 1)]};	}) `uvm_error(this.get_name(), "randomization error")
			otp_writer.add_entry(e);
			entries.push_back(e);
		end
		
		otp_writer.write(file_name);
		reset(file_name);
		
		registers.check_register(regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_STATUS, 0);
		
		for (int i = 0; i < 4096; i++) begin
			uvm_reg_data_t value;
			address_data_otp_entry entry = entries[i/4];
			
			registers.write_and_check_register(regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_ADDRESS, i);
			
			regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_STATUS.read(status, value);
			if(value != 2) `uvm_error(this.get_name(), $sformatf("Read unexpected READ STATUS value at OTP index %0d, expected 0x0002, got 0x%0h", i, value))
			
			regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_VALUE.read(status, value);
			if(i % 4 == 0 && entry.ecc_address[23:12] != 12'(value)) `uvm_error(this.get_name(), $sformatf("Read unexpected value at OTP index %0d, expected 0x%0h, got 0x%0h", i, entry.ecc_address[23:12], value))
			if(i % 4 == 1 && entry.ecc_address[11:0]  != 12'(value)) `uvm_error(this.get_name(), $sformatf("Read unexpected value at OTP index %0d, expected 0x%0h, got 0x%0h", i, entry.ecc_address[11:0], value))
			if(i % 4 == 2 && entry.ecc_data[23:12]    != 12'(value)) `uvm_error(this.get_name(), $sformatf("Read unexpected value at OTP index %0d, expected 0x%0h, got 0x%0h", i, entry.ecc_data[23:12], value))
			if(i % 4 == 3 && entry.ecc_data[11:0]     != 12'(value)) `uvm_error(this.get_name(), $sformatf("Read unexpected value at OTP index %0d, expected 0x%0h, got 0x%0h", i, entry.ecc_data[11:0], value))
		end
	endtask
endclass
