localparam int unsigned WAVESHAPE_REG_COUNT = 72+72;

class register_access_wave_shaping_registers_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_access_wave_shaping_registers_seq)
	
	function new(string name = "");
		super.new("register_access_wave_shaping_registers");
	endfunction : new

	
	virtual task run_tests();
		spi_read_master_register_seq read_seq;
		logic[15:0] values[$];
		logic[11:0] addresses[$];
		
		log_sim_description($sformatf("access wave shaping registers using write master register and burst read"), LOG_LEVEL_SEQUENCE);
		
		repeat(10) begin
			values.delete();
			addresses.delete();
			
			// write all
			for (int i=0; i< int'(WAVESHAPE_REG_COUNT); i++) begin
				spi_write_master_register_seq write_seq;
				`spi_frame_begin
					`spi_frame_send(write_seq, address == 12'(project_pkg::BASE_ADDR_WAVESHAPING + i); data <= 16'h1F;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				addresses.push_back(write_seq.address);
				values.push_back(write_seq.data);
			end
			
			#100us;	
			
			// read all
			`spi_frame_begin
				`spi_frame_send(read_seq, address == 0; burst_addresses.size() == addresses.size(); foreach(burst_addresses[i]) burst_addresses[i] ==  addresses[i]; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			for (int i=0; i< values.size(); i++) begin
				if(values[i] != read_seq.burst_data[i]) `uvm_error(this.get_name(), $sformatf("Read unexpected value in wave shaping register of index %0d at address 0x%0h, expected 0x%0h, got 0x%0h", i, addresses[i], values[i], read_seq.burst_data[i]))
			end	
		end
	endtask
endclass