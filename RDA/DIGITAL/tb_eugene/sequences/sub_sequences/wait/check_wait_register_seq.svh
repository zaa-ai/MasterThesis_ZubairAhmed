class check_wait_register_seq extends base_wait_seq;
	
	`uvm_object_utils(check_wait_register_seq) 
    
	function new(string name = "");
		super.new("check_wait_register");
	endfunction : new

	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme = new();
		logic[14:0] wait_time = 15'h7FFF;
		
		log_sim_description("check WAIT_TIME register", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		`spi_frame_begin
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == local::wait_time;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		fork
			begin
				#10us;
				expect_wait_time_for_all_channels(int'(wait_time), 20);
			end
			begin
				#1ms;
				expect_wait_time_for_all_channels(int'(wait_time)-1000, 20);
			end
			begin
				#2ms;
				expect_wait_time_for_all_channels(int'(wait_time)-2000, 20);
			end
			begin
				#3ms;
				expect_wait_time_for_all_channels(int'(wait_time)-3000, 20);
			end
			begin
				#4ms;
				expect_wait_time_for_all_channels(int'(wait_time)-4000, 20);
			end
			begin
				#10ms;
				// stop
				`spi_frame_begin
					`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#100us;
				expect_wait_time_for_all_channels(0);
			end
		join
		#1ms;
	endtask
endclass
