class pdcm_random_denso_scheme_on_all_channels_seq extends base_dsi_master_seq;
	
	rand int pulse_count;
	
	`uvm_object_utils_begin (pdcm_random_denso_scheme_on_all_channels_seq)
		`uvm_field_int (pulse_count, UVM_DEFAULT | UVM_DEC )
	`uvm_object_utils_end
	
	constraint co_pulse_count {soft pulse_count inside {[1:10]};}
	
	function new(string name = "");
		super.new("pdcm_random_denso_scheme_on_all_channels");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = create_tdma_scheme();

		log_sim_description($sformatf("PDCM with Denso TDMA scheme and %0d periods on all channels", pulse_count), LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		#100us;
		check_dab(1'b1);
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'(local::pulse_count);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		fork
			begin
				#(scheme.pdcm_period * 1us + 20us);
				check_dab(1'b0);
			end
			begin
				#(pulse_count * scheme.pdcm_period * 1us);
			end
		join
		
		repeat(pulse_count) begin
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#10us;
		end
		check_dab(1'b1);
		#100us;
	endtask
	
	virtual function tdma_scheme_pdcm create_tdma_scheme();
		tdma_scheme_pdcm_denso denso_scheme = new();
		return denso_scheme;
	endfunction
endclass