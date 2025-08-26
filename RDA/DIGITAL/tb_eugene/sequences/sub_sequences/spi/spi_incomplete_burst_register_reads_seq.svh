class spi_incomplete_burst_register_reads_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_burst_register_reads_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_burst_register_reads");
	endfunction
	
	virtual task run_tests();
		log_sim_description("send incomplete burst read master register commands", LOG_LEVEL_SEQUENCE);
		
		repeat(5) begin
			int expected_word_count;
			logic[11:0] addresses[$];
			
			// add some random burst addresses
			repeat($urandom_range(1,10)) begin
				randcase
					1:addresses.push_back(ADDR_INFO_IC_REVISION);
					1:addresses.push_back(ADDR_INTERRUPT_IRQ_STAT);
					1:addresses.push_back(ADDR_INTERRUPT_IRQ_MASK);
					1:addresses.push_back(ADDR_DSI_0_DSI_STAT);
					1:addresses.push_back(ADDR_DSI_1_DSI_STAT);
					1:addresses.push_back(ADDR_DSI_0_PDCM_PERIOD);
					1:addresses.push_back(ADDR_DSI_1_PDCM_PERIOD);
				endcase
			end
			expected_word_count = 1 + addresses.size() + 1;
			
			`spi_frame_begin
				`spi_frame_create(spi_incomplete_read_master_register_seq, address == 12'(ADDR_SUPPLY_SUP_STAT); word_count inside {[2:expected_word_count-1]}; burst_addresses.size() == addresses.size(); foreach(burst_addresses[i]) burst_addresses[i] ==  addresses[i];)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#10us;
			`spi_frame_begin
				`spi_frame_create(spi_read_status_seq,)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end_with_status('{SCI, NT0, NT1})
			#50us;			
			`create_and_send(spec_CRM_command_seq)
		end
	endtask
endclass

