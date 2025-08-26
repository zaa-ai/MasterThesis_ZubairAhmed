class dsi3_discovery_mode_overflow_seq extends base_dsi_master_seq;

	rand logic[project_pkg::DSI_CHANNELS-1:0] channels;
	
	`uvm_object_utils(dsi3_discovery_mode_overflow_seq)

	function new(string name = "");
		super.new("dsi3_discovery_mode_overflow");
	endfunction : new

	virtual task run_tests();
		
		log_sim_description($sformatf("discovery mode overflow at channels 0b%2b", channels), LOG_LEVEL_SEQUENCE);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel] == 1'b1) begin
				tdma_scheme dm_scheme = tdma_scheme_dm::valid(16);
				set_tdma_scheme_dm(channel, dm_scheme);
			end
		end
		
		transaction_recorder.enable_recorder();		
				
		`spi_frame_begin
			`spi_frame_create(spi_discovery_mode_seq, channel_bits == channels;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#(edf_parameters.epms.t__Disc_per_8__.get_typ_time() * 16);
		#100us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel] == 1'b1) begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.SLAVES, 15);
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DMOF, 1'b1);
				transaction_recorder.expect_tr_count(channel, 16);
				// clear DMOF IRQ
				regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DMOF.write(status, 1'b1);
			end
		end
		transaction_recorder.disable_recorder();
		#200us;
	endtask
	
	
endclass