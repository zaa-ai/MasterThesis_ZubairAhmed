class pdcm_denso_one_moving_packet_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_denso_one_moving_packet_seq)
	
	function new(string name = "");
		super.new("pdcm_denso_one_moving_packet");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme = new();

		log_sim_description("PDCM with one single moving packet", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		check_dab(1'b1);
		
		for (int packet_start = 30; packet_start < 880; packet_start += 10) begin
			tdma_scheme_pdcm_denso modified_scheme = new();
			
			if(is_borderline_timing(scheme, packet_start)) begin
				`uvm_info(this.get_name(), $sformatf("skipped start time %0d becaus of gray zone timing", packet_start), UVM_MEDIUM)
				continue;
			end
			
			log_sim_description($sformatf("PDCM with single packet at %0dus start", packet_start), LOG_LEVEL_OTHERS);
			
			modified_scheme.packets[0].set_start_time_window(packet_start, packet_start);
			for (int i = 1; i < modified_scheme.packets.size(); i++) begin
				modified_scheme.packets[i].enable = 1'b0;
			end
			
			set_tdma_scheme_pdcm(0, modified_scheme);
			set_tdma_scheme_pdcm(1, modified_scheme);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us);
			check_dab(1'b0);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			check_dab(1'b1);
			#50us;
		end
	endtask
	
	function bit is_borderline_timing(tdma_scheme_pdcm_denso scheme, int packet_start);
		for (int i = 1; i < scheme.packets.size(); i++) begin
			int previous_latest_start = int'(scheme.packets[i-1].latest_start_time);
			int next_earliest_start = int'(scheme.packets[i].earliest_start_time);
			if(packet_start > previous_latest_start && packet_start < next_earliest_start) begin
				int borderline = previous_latest_start + ((next_earliest_start - previous_latest_start) / 2);
				if(packet_start > borderline - 5 && packet_start < borderline + 5) begin
					return 1'b1;					
				end
			end
		end
		return 1'b0;
	endfunction
endclass