class spi_hw_fail_during_spi_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_hw_fail_during_spi_frame_seq)
	
	function new(string name = "");
		super.new("spi_hw_fail_during_spi_frame");
	endfunction
	
	virtual task run_tests();
		`ifndef GATE_LEVEL
			do_run_tests();
		`endif
	endtask
	
	virtual task do_run_tests();
		log_sim_description("apply a HW_FAIL within a SPI frame", LOG_LEVEL_SEQUENCE);
		
		
		
		transaction_recorder.enable_recorder();
		transaction_recorder.clear_all();
		clear_all_irqs();
		// invalidate all TDMA schemes
		`spi_frame_begin
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;	
		
		check_intb(1'b1);
		
		get_checker_config().disable_all_master_transmission_checkers();
		get_checker_config().enable_mirroring_check = 1'b0;
		
		fork
			begin
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
				`spi_frame_end
			end
			begin
				#7us;
				hdl_force(`STRING_OF(`SPI_STATE_PATH), 'hF);
				#500ns;
				hdl_release(`STRING_OF(`SPI_STATE_PATH));
			end
		join
		
		get_checker_config().enable_mirroring_check = 1'b1;
			
		#1ms;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			transaction_recorder.expect_tr_count(channel, 0);
		end
		check_intb(1'b0); // HW_FAL IRQ
		
		`spi_frame_begin
			`spi_frame_create(spi_reset_seq,)
		`spi_frame_end_with_status({SCI, HE, NT0, NT1})
		
		registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.HW_FAIL, 64'b1);
		registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 64'b1);
		// clear HW and all other IRQs
		clear_all_irqs();
		
		get_checker_config().enable_all_master_transmission_checkers();
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
		`spi_frame_end_with_status({NT0, NT1})
		
		#500us;
		`spi_frame_begin
			`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
		`spi_frame_end
		#10us;
	endtask
endclass