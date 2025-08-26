
typedef	enum shortint {
	INITIAL	= 0, 
	BUSY	= 1, 
	READY	= 2,
	FAIL	= 3
} otp_read_status_t;

class trimming extends uvm_report_object;
	
	rand logic[15:0] data;
	
	string port_name;
	uvm_reg register;
	int maximum;
    
    protected simulation_logger logger;
	
	constraint co_data { data inside {[0:maximum]};}
		
	function new(uvm_reg register, string port_name);
		super.new("otp_trimming");
		this.port_name = port_name;
		this.register = register;
		this.maximum = max_value(register);
		if(!this.randomize()) `uvm_error(this.get_name(), "randomization error")
		logger = new("sim_logger");
		`uvm_info(this.get_type_name(), $sformatf("created trimming for register %s (max value %0d) to random value 0x%0h", register.get_name(), maximum, data), UVM_MEDIUM)
	endfunction 
	
	virtual function string get_type_name (); return "trimming"; endfunction
	
	/**
	 * Gets maximum value of given register from all contained fields.
	 */
	function automatic int max_value(uvm_reg register);
		uvm_reg_field fields[$];
		int bit_width;
		
		bit_width = 0;
		register.get_fields(fields);
		
		foreach(fields[i]) begin
			bit_width += fields[i].get_n_bits();
		end
		return (2**bit_width) - 1;
	endfunction
	
	virtual task check_register_value();
		uvm_status_e status;
		uvm_reg_data_t value;
		
		register.read(status, value);
		if(value != 64'(data)) `uvm_error(this.get_name(), $sformatf("Unexpected data in trim register %s, expected 0x%0h, got 0x%0h.", register.get_name(), data, value));
		if(status != UVM_IS_OK) `uvm_error(this.get_name(), $sformatf("Failed to read value of registrer %s, UVM status is not OK.", register.get_name()))
        logger.log_sim_check(register.get_name(), , "PASS");
	endtask
	
	virtual task check_port_value();
		if(port_name != "") begin
			check_path_for_value({`STRING_OF(`xdig_path), ".", port_name}, data);
		end
	endtask
	
	virtual function void check_path_for_value(string path, int expected_value);
		int value;
		if (!uvm_hdl_read(path, value)) `uvm_error(this.get_type_name(), $sformatf("reading of path %s failed", path))
		if (value != expected_value) `uvm_error(this.get_type_name(), $sformatf("Trimming output for register '%s' at port %s is NOT correct! Expected 0x%0h but got 0x%0h", register.get_name(), path, expected_value, value))
	endfunction
	
endclass

class dsi_rec_trimming extends trimming;
		
	int channel;
	bit rx;
		
	function new(uvm_reg register, int channel, bit rx);
		super.new(register, "");
		this.channel = channel;
		this.rx = rx;
	endfunction
	
	virtual task check_port_value();
		int lsb = 0 + 4*channel;
		int msb = 3 + 4*channel;
		string port_rx1   = $sformatf("O_TRIM_DSI_RX1[%0d:%0d]", msb, lsb);
		string port_rx2   = $sformatf("O_TRIM_DSI_RX2[%0d:%0d]", msb, lsb);
		string select_rx1 = $sformatf("I_DSI_RXD1[%0d]", channel);
		string select_rx2 = $sformatf("I_DSI_RXD2[%0d]", channel);
		
		if (!uvm_hdl_force({`STRING_OF(`xdig_path), ".", select_rx1}, rx)) `uvm_error(this.get_type_name(), $sformatf("forcing of path %s failed", {`STRING_OF(`xdig_path), ".", select_rx1}))
		if (!uvm_hdl_force({`STRING_OF(`xdig_path), ".", select_rx2}, rx)) `uvm_error(this.get_type_name(), $sformatf("forcing of path %s failed", {`STRING_OF(`xdig_path), ".", select_rx2}))
		#100ns;
		check_path_for_value({`STRING_OF(`xdig_path), ".", port_rx1}, data[3:0]);
		check_path_for_value({`STRING_OF(`xdig_path), ".", port_rx2}, data[7:4]);
		#100ns;
		if (!uvm_hdl_release({`STRING_OF(`xdig_path), ".", select_rx1})  ) `uvm_error(this.get_type_name(), $sformatf("releasing of path %s failed", {`STRING_OF(`xdig_path), ".", select_rx1}))
		if (!uvm_hdl_release({`STRING_OF(`xdig_path), ".", select_rx2})  ) `uvm_error(this.get_type_name(), $sformatf("releasing of path %s failed", {`STRING_OF(`xdig_path), ".", select_rx2}))
	endtask
	
endclass

class random_trimming extends uvm_object;
		
	rand logic[15:0] data;
	rand logic[11:0] address;
	
	`uvm_field_utils_begin(random_trimming)
		`uvm_field_int (data,    UVM_DEFAULT | UVM_NORECORD| UVM_HEX)
		`uvm_field_int (address, UVM_DEFAULT | UVM_NORECORD| UVM_HEX)
	`uvm_field_utils_end
		
	function new();
		super.new("random trimming");
	endfunction 
	
endclass

//=============================================================================

class base_otp_seq extends base_dsi_master_seq;

	`uvm_object_utils(base_otp_seq)
	
	function new(string name = "base_otp_seq");
		super.new(name);
	endfunction
	
	function void init_trimmings(ref trimming trimmings[$]);
		trimmings = {};
		
		trimmings.push_back(create_trimming(regmodel.Info.IC_revision_and_ID_registers.CHIP_ID_LOW,	 	""));
		trimmings.push_back(create_trimming(regmodel.Info.IC_revision_and_ID_registers.CHIP_ID_HIGH, 	""));
		trimmings.push_back(create_trimming(regmodel.Supply.supply_registers.TRIM_IREF, 				"O_TRIM_I5U"));
		trimmings.push_back(create_trimming(regmodel.Supply.supply_registers.TRIM_OT, 					"O_TRIM_OT"));
		trimmings.push_back(create_trimming(regmodel.Supply.supply_registers.IO_CTRL,	 				"O_PAD_DS"));
		trimmings.push_back(create_trimming(regmodel.Timebase.time_base_registers.TRIM_OSC, 			"O_TRIM_OSC_F"));
		trimmings.push_back(create_trimming(regmodel.Timebase.time_base_registers.TRIM_OSC_TCF, 		"O_TRIM_OSC_TCF"));
		
		// channel related trimmings
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi_rec_trimming rec_rise = new(regmodel.DSI_TRIMMING[channel].DSI3_channel_trimming_registers.TRIM_DSI_REC_RISE, channel, 1'b0);
			dsi_rec_trimming rec_fall = new(regmodel.DSI_TRIMMING[channel].DSI3_channel_trimming_registers.TRIM_DSI_REC_FALL, channel, 1'b1);
			trimmings.push_back(rec_rise);
			trimmings.push_back(rec_fall);
		end
	endfunction
	
	function void write_trimmings(trimming trimmings[$], string file_name );
		ecc_otp_writer otp_writer = new();
		foreach(trimmings[i]) begin
			logic[15:0] address = 16'(trimmings[i].register.get_address());
			logic[15:0] data = trimmings[i].data;
			otp_writer.add_address_data(address, data);
		end
		otp_writer.write(file_name);
	endfunction
	
	function automatic trimming create_trimming(uvm_reg register, string port_name);
		trimming tr;
		tr = new(register, port_name);
		return tr;
	endfunction
	
	task check_otp_fail_irq(bit expected_fail);
		registers.check_flag(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.OTPFAIL, uvm_reg_data_t'(expected_fail));
	endtask
	
	task check_trimmings(trimming trimmings[$], otp_read_status_t expected_status, int trimming_count = 1024);
		foreach(trimmings[i]) begin
			if(i < trimming_count) begin
				uvm_reg_addr_t address = trimmings[i].register.get_address();
				logic[15:0] data = trimmings[i].data;
				
				check_trimming(i*4 + 0,	address[15:8], expected_status);
				check_trimming(i*4 + 1,	address[7:0],  expected_status);
				check_trimming(i*4 + 2,	data[15:8],    expected_status);
				check_trimming(i*4 + 3, data[7:0],     expected_status);
			end
		end
	endtask
	
	task check_trimming(int otp_index, logic[7:0] expected_data, otp_read_status_t expected_status);
		otp_read_status_t	current_status;
		
		registers.write_and_check_register(regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_ADDRESS, otp_index);
		#200ns;
		read_and_check_OTP_READ_STATUS(expected_status, otp_index, current_status);
		// only check data if status is READY
		if(expected_status == READY) begin
			if(current_status != READY) `uvm_error(this.get_name(), $sformatf("Read unexpected READ STATUS value at OTP index %1d, expected 0x2 (ready), got %s", otp_index, current_status.name()))
			else begin
				uvm_reg_data_t value;
				regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_VALUE.read(status, value);
				if(value[7:0] != expected_data) `uvm_error(this.get_name(), $sformatf("Read unexpected value at OTP index %0d, expected 0x%0h, got 0x%0h", otp_index, value[7:0], expected_data))
			end
		end
	endtask
	
	virtual task wait_for_1us_tick();
		wait_for_tick_equals(1'b0);
		wait_for_tick_equals(1'b1);
	endtask
	
	task wait_for_tick_equals(logic value);
		uvm_hdl_data_t	tick;
		string path = {`STRING_OF(`LOGIC_TOP_PATH),".timebase_info.tick_1us"};
		do begin 
			tick = hdl_read(path);
			#10ns;
		end while (tick[0] != value);
	endtask
	
	task read_and_check_OTP_READ_STATUS(otp_read_status_t expected_status, int otp_index, output otp_read_status_t	current_status);
		get_OTP_READ_STATUS(current_status);
		if(current_status != expected_status) `uvm_error(this.get_name(), $sformatf("Read unexpected READ STATUS value at OTP index %0d, expected %s, got %s", otp_index, expected_status.name(), current_status.name()))
	endtask
	
	task get_OTP_READ_STATUS(output otp_read_status_t	current_status);
		uvm_reg_data_t value;
		regmodel.OTP_CTRL.OTP_readout_register.OTP_READ_STATUS.read(status, value);
		current_status = otp_read_status_t'(value);
	endtask
endclass