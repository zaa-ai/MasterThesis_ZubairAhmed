class measure_t_dsi3_sync_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(measure_t_dsi3_sync_seq) 
	
	function new(string name = "");
		super.new("measure_t_dsi3_sync");
	endfunction
	
	virtual task run_tests();
		int delay;
		time posedge_csb, negedge_channel0, delay_command_to_CRM;
		time first_delay_command_to_CRM = 0ns;
		bit crm_sent = 1'b0;
		
		log_sim_description("measure t__DSI3,sync__", LOG_LEVEL_SEQUENCE);
		
		m_spi_agent.m_config.csb_handler = per_frame_csb_hander::create(); 
		
		for (delay = 100; delay < 5000; delay += 100) begin
			log_sim_description($sformatf("apply SYNCB with a delay of %0dns", delay), LOG_LEVEL_OTHERS);
			transaction_recorder.enable_recorder();
			set_syncb(1'b0);
			
			fork
				`spi_frame_begin
					`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				begin
					@(posedge m_spi_agent.m_config.vif.CSN);
					#(delay * 1ns);
					set_syncb(1'b1);
					#1us;
					set_syncb(1'b0);
				end
				begin
					fork
						begin
							@(posedge m_spi_agent.m_config.vif.CSN);
							posedge_csb = $time();
							@(negedge m_dsi3_master_agent[0].m_config.vif.cable.Voltage);
							negedge_channel0 = $time();
							delay_command_to_CRM = negedge_channel0 - posedge_csb;
							crm_sent = 1'b1;
						end
						begin // timeout
							#200us;
							`spi_frame_begin
								`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == '1; )
								`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
							`spi_frame_end
						end
					join_any
					disable fork;
				end
			join
			#500us;
			if (crm_sent == 1'b1) begin
				log_sim_measure ("t__DSI3,sync__", $sformatf("%0f", (delay/1000.0)));
				break;
			end
		end
		if (crm_sent == 1'b0) begin
			`uvm_error(this.get_type_name(), $sformatf("Synchronisation seems to be wrong, no CRM has been transmitted"))
		end		
		transaction_recorder.disable_recorder();
		// restore default CSB handling
		m_spi_agent.m_config.csb_handler = per_word_csb_hander::create(); 
	endtask
	
endclass