class stop_random_command_queue_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(stop_random_command_queue_seq) 
	
	function new(string name = "");
		super.new("stop_random_command_queue");
	endfunction

	/**
	 * Try to stop/clear a random queue of commands. 
	 */
	virtual task run_tests();
		log_sim_description("stop a queue of random commands", LOG_LEVEL_SEQUENCE);
		
		repeat(20) begin
			get_checker_config().disable_all_master_transmission_checkers();

			`spi_frame_begin
				spi_frame_factory#()::append_random_commands(frame, $urandom_range(5,10));
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
				
			#2ms;
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#5ms;
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)  // clear all buffers 
				`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'd0;) // clear all TDMA schemes
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
			// re-enable checker again 
			get_checker_config().enable_all_master_transmission_checkers();

			
			// read DSI_CMD registers
			foreach (regmodel.DSI[channel]) begin
				registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.DSI_CMD, 0);
			end
			
				
			randcase
				1 : begin
					`create_and_send(spec_CRM_command_seq)
				end
				1 : begin
					`create_and_send(spec_single_frame_pdcm_read_seq) 
				end
			endcase
		end
	endtask
endclass