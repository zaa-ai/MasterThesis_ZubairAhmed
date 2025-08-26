class register_spi_burst_read_zero_address_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_spi_burst_read_zero_address_seq)
	
	function new(string name = "");
		super.new("register_spi_burst_read_zero_address");
	endfunction : new
	
	virtual task run_tests();
		spi_read_master_register_seq read_seq;
		logic[15:0] value_ram;
		log_sim_description("multiple SPI burst reads using zero as address", LOG_LEVEL_SEQUENCE);
		
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 12'(project_pkg::BASE_ADDR_RAM); burst_addresses.size() == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
        value_ram = read_seq.data;
		
		repeat(5) begin
			`spi_frame_begin
				`spi_frame_send(read_seq, address == 12'd0; burst_addresses.size() == 1; burst_addresses[0] == 12'(project_pkg::BASE_ADDR_RAM);)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end   
			
			if(read_seq.burst_data[0] != value_ram) begin 
				`uvm_error(this.get_type_name(), $sformatf("read unexpected value during burst read, expected %04h, got %04h", value_ram, read_seq.burst_data[0]));     
			end
			#1us;
		end	
	endtask
endclass