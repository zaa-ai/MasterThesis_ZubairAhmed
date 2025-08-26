class pdcm_denso_scheme_all_source_ids_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_denso_scheme_all_source_ids_seq)
	
	function new(string name = "");
		super.new("pdcm_denso_scheme_all_source_ids");
	endfunction : new
	
	virtual task run_tests();
		dsi3_pkg::sid_length_e source_id;
        
        check_crc('{16'hd1ba}, 16'ha447); // packet 0
        check_crc('{16'h4470}, 16'h3b5f); // packet 3
        check_crc('{16'hf72a}, 16'h8bbe); // packet 4
        check_crc('{16'h7434}, 16'h368a); // packet 5
        
		log_sim_description("PDCM with Denso TDMA scheme and all different SID variante on all channels", LOG_LEVEL_SEQUENCE);
		
		source_id = source_id.first();
		do begin
			tdma_scheme_pdcm_denso scheme = new();
			
			log_sim_description($sformatf("PDCM with Denso TDMA scheme and SID = %s", source_id.name()), LOG_LEVEL_OTHERS);
			
			scheme.set_source_id_for_all_packets(source_id);
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
			set_tdma_scheme_pdcm(0, scheme);
			set_tdma_scheme_pdcm(1, scheme);
			
			#100us;
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us);
			
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
			source_id = source_id.next();
		end while (source_id != source_id.first());
    endtask
    
    virtual function void check_crc(logic[15:0]  data[$], logic[15:0] crc);
        logic[15:0] expected_crc;
        logic[3:0]  data_4[$];
        void'(convert_queue #(16, 4)::convert(data, data_4));
        expected_crc = crc_calculation_pkg::dsi3_calculate_crc(1, data_4, dsi3_pkg::SID_16Bit_CRC);
        if (crc != expected_crc)
            `uvm_error(this.get_type_name(), $sformatf("CRC of 0x%4h is wrong! Got 0x%4h, but expected 0x%4h", data[0], crc, expected_crc))
    endfunction
endclass