class stop_command_queue_within_command_frame_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(stop_command_queue_within_command_frame_seq) 
	
	function new(string name = "");
		super.new("stop_command_queue_within_command_frame");
	endfunction
	
	/**
	 * Stop command queue directly inside a SPI command frame.
	 */
	virtual task run_tests();
	
		log_sim_description("stop command queue command within a SPI frame", LOG_LEVEL_SEQUENCE);

		get_checker_config().disable_all_master_transmission_checkers();

		repeat(30) begin
			`spi_frame_begin
				spi_frame_factory#()::append_random_commands(frame, $urandom_range(5,10), 1'b0);
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
				
			#500us;

			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#5ms;
			
			// read DSI_CMD registers
			foreach (regmodel.DSI[channel]) begin
				registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.DSI_CMD, 0);
			end
			#100us;
		end
		
		// re-enable checker again
		get_checker_config().enable_all_master_transmission_checkers();
			
		randcase
			1 : begin
				`create_and_send(spec_CRM_command_seq)
			end
			1 : begin
				`create_and_send(spec_single_frame_pdcm_read_seq) 
			end
		endcase
	endtask
endclass