class crm_read_status_during_reception_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(crm_read_status_during_reception_seq)

	function new(string name = "");
		super.new("crm_read_status_during_reception");
	endfunction
	
	task run_tests();
		bit crm_finished = 1'b0;
		log_sim_description("read IC status during CRM transmission on all channels", LOG_LEVEL_SEQUENCE);
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		fork
			begin
				#450us;
				crm_finished = 1'b1;
			end
			begin
				while(crm_finished == 1'b0) begin
					`spi_frame_begin
						`spi_frame_create(spi_read_status_seq,)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
				end
			end
		join
		
		`spi_frame_begin
			`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
	endtask
endclass
