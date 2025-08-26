class pdcm_ram_burst_read_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_ram_burst_read_seq)

	function new(string name = "");
		super.new("pdcm_ram_burst_read");
	endfunction
	
	task run_tests();
		tdma_scheme_pdcm_denso_15 scheme = new();
		logic[7:0] period_count = 8'd16;
		logic[7:0] current_period = 8'd0;

		log_sim_description($sformatf("PDCM on all channels and RAM burst read"), LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == period_count;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		fork
			begin
				#(scheme.pdcm_period * 1us);
				while(current_period < period_count) begin
					burst_read_ram();
				end
			end
			begin
				forever begin
					#(scheme.pdcm_period * 1us);
					current_period += 8'd1;
				end
			end
		join_any
		
		repeat(period_count) begin	
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end
	endtask
	
	task burst_read_ram();
		logic[11:0] addresses[$];
		// collect all RAM addresses
		for (int i=int'(project_pkg::BASE_ADDR_RAM); i< int'(project_pkg::BASE_ADDR_RAM + project_pkg::SIZE_RAM); i++) begin
			addresses.push_back(12'(i));
		end
		// read RAM
		`spi_frame_begin
			`spi_frame_create(spi_read_master_register_seq, address == 0; burst_addresses.size() == addresses.size(); foreach(burst_addresses[i]) burst_addresses[i] ==  addresses[i]; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
	endtask
endclass
