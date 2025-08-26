class register_miso_crc_example_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_miso_crc_example_seq)
	
	function new(string name = "");
		super.new("register_miso_crc_example");
	endfunction : new
	
	virtual task run_tests();
		spi_any_command_seq any_seq;
		logic[15:0] miso_crc;
		logic[15:0] miso_data[$];
		log_sim_description("example of MISO crc calculation", LOG_LEVEL_SEQUENCE);
		
		`spi_frame_begin
		`spi_frame_send(any_seq,)
		any_seq.command_words = {16'h5102, 16'h0071, 16'h5103, 16'h03e7, 16'h1000, 16'hF47F};
		`spi_frame_end
		
		miso_data = any_seq.data_out;
		miso_data.pop_back();
		miso_crc = crc_calculation_pkg::spi_calculate_correct_crc(miso_data);
			
		if(any_seq.data_out[$] != miso_crc) `uvm_error(this.get_name(), $sformatf("Unexpected MISO CRC value, expected %0h, got %0h.", miso_crc, any_seq.data_out[$]))
			
		#50us;
	endtask
endclass