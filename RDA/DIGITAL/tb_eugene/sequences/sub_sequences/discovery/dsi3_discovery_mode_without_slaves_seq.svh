class dsi3_discovery_mode_without_slaves_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(dsi3_discovery_mode_without_slaves_seq)

	function new(string name = "");
		super.new("dsi3_discovery_mode_without_slaves");
	endfunction : new

	virtual task run_tests();
		tdma_scheme dm_scheme = tdma_scheme_dm::valid(0);
		
		log_sim_description($sformatf("discovery mode without any connected slave on all channels"), LOG_LEVEL_SEQUENCE);
		
		set_tdma_scheme_dm(0, dm_scheme);
		set_tdma_scheme_dm(1, dm_scheme);
		
		transaction_recorder.enable_recorder();		
				
		`spi_frame_begin
			`spi_frame_create(spi_discovery_mode_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#(edf_parameters.epms.t__Disc_per_8__.get_typ_time());
		#100us;
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.SLAVES, 0);
			registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DMOF, 1'b0);
			transaction_recorder.expect_tr_count(channel, 1);
		end
		transaction_recorder.disable_recorder();
		#200us;
	endtask
	
	
endclass