class base_wait_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(base_wait_seq) 
    
	function new(string name = "base_wait_seq");
		super.new(name);
	endfunction

	task expect_wait_time_for_all_channels(int time_value, int tol=0);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			expect_wait_time(channel, time_value, tol);
		end
	endtask
	
	task expect_wait_time(int channel, int time_value, int tol=0);
		uvm_reg_data_t value;
		int diff;
		regmodel.DSI[channel].DSI3_channel_registers.WAIT_TIME.read(status, value);
		diff = int'(value) > time_value ? (int'(value) - time_value) : (time_value - int'(value));
		if(diff > tol) `uvm_error(this.get_name(), $sformatf("Read unexpected value from WAIT_TIME register of channel %0d, expected %0h, got %0h. Tolerance is %0d.", channel, time_value, value, tol))
	endtask
endclass

