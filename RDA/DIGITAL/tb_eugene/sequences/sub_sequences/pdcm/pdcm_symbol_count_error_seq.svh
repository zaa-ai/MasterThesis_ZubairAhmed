class pdcm_symbol_count_error_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_symbol_count_error_seq)

	function new(string name = "");
		super.new("pdcm_symbol_count_error");
	endfunction : new
	
	task run_tests();
		log_sim_description($sformatf("symbol count error for all packets of a Denso TDMA scheme"), LOG_LEVEL_SEQUENCE);
		
		// send one more symbol for each packet
		pdcm_with_symbol_count_error(1);
		// send one symbol less for each packet
		pdcm_with_symbol_count_error(-1);
	endtask
	
	task pdcm_with_symbol_count_error(int symbol_count_offset);
		tdma_scheme_pdcm_denso_15 scheme = new();

		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		#50us;
		
		foreach (scheme.packets[packet_index]) begin
			log_sim_description($sformatf("symbol count error at packet index %0d, symbol count offset %0d", packet_index, symbol_count_offset), LOG_LEVEL_OTHERS);
			set_tdma_scheme_pdcm(0, scheme);
			set_tdma_scheme_pdcm(1, scheme);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
			
			@(negedge m_dsi3_master_agent[0].m_config.vif.cable.Voltage or negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
			set_symbol_count(scheme, packet_index, symbol_count_offset);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			@(negedge m_dsi3_master_agent[0].m_config.vif.cable.Voltage or negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
			set_symbol_count(scheme, packet_index, 0);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(scheme.pdcm_period * 1us);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end
	endtask

	function void set_symbol_count(tdma_scheme_pdcm scheme, int packet_index, int symbol_count_offset);
		foreach (scheme.packets[i]) begin
			if(i == packet_index) begin
				scheme.packets[i].symbol_count = 8 + symbol_count_offset;
			end
		end
	endfunction
endclass
