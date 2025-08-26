class dsi_enable_ignore_new_commands_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_enable_ignore_new_commands_seq) 
    
	function new(string name = "");
		super.new("dsi_enable_ignore_new_commands");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		log_sim_description("ignore new DSI commands if DSI_ENABLE.TRE is disabled", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_pdcm(channel, scheme);
		end
		
		
		for (int aborted_channel=1; aborted_channel < 2 ** project_pkg::DSI_CHANNELS; aborted_channel++) begin
			transaction_recorder.clear_all();
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 8'd1;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;	
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 1'b0);			
			disable_dsi_channels(2'(aborted_channel));
			#50us;
			clear_all_irqs();
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(scheme.pdcm_period * 1us + 500us);
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				int tr_count = transaction_recorder.get_master_tr_count(channel);
				if(aborted_channel[channel] == 1'b1) begin
					registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
					if(tr_count != 1) begin
						`uvm_error(this.get_type_name(), $sformatf("channel %0d is disabled but there seem to be transactions, expected 0, got %0d!", channel, tr_count))
					end
				end
				else begin
					registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
					if(tr_count != 3) begin
						`uvm_error(this.get_type_name(), $sformatf("channel %0d is enabled but there where not transaction, expected %0d, got %0d!", channel, 2, tr_count))
					end
				end
			end

			// enable all channels
			enable_dsi_channels(2'b11);
			transaction_recorder.clear_all();
			#50us
					
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b10; pulse_count == 8'd1;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;	

			#(scheme.pdcm_period * 1us);
			transaction_recorder.expect_tr_count_for_all_channels(1);
	
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end	
	endtask
endclass

