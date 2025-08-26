class register_spi_burst_read_to_improve_coverage_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_spi_burst_read_to_improve_coverage_seq)
	
	function new(string name = "");
		super.new("register_spi_burst_read_to_improve_coverage");
	endfunction : new
	
	virtual task run_tests();
		spi_read_master_register_seq read_seq;
		log_sim_description("SPI burst read higher areas of address space", LOG_LEVEL_SEQUENCE);
		
		repeat(20) begin
			`spi_frame_begin
				`spi_frame_send(read_seq, address == 0; burst_addresses.size() inside {[100:200]}; foreach(burst_addresses[i]) burst_addresses[i] >  12'h400;)
				`spi_frame_create(spi_tx_crc_request_seq,)
			`spi_frame_end
		end	
	endtask
endclass