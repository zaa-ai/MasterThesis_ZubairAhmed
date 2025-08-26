class dsi_enable_abort_discovery_mode_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_enable_abort_discovery_mode_seq) 
    
	function new(string name = "");
		super.new("dsi_enable_abort_discovery_mode");
	endfunction

	virtual task run_tests();
		log_sim_description("abort Discovery Mode using DSI_ENABLE register", LOG_LEVEL_SEQUENCE);
		
		// 15 slaves
		set_tdma_scheme_dm(0, tdma_scheme_dm::valid());
		set_tdma_scheme_dm(1, tdma_scheme_dm::valid());
		
		repeat(10) begin
			int abort_slave_count = $urandom_range(1, 15);
			
			log_sim_description($sformatf("abort Discovery Mode after slave number %0d using DSI_ENABLE register", abort_slave_count), LOG_LEVEL_OTHERS);
			
			`spi_frame_begin
				`spi_frame_create(spi_discovery_mode_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			wait_for_voltage_edge_at_channel(0, 100us);
			#50us;
			#(abort_slave_count * edf_parameters.epms.t__Disc_per_8__.get_typ_time());
			disable_dsi_channels(2'b11);
			#100us;
			enable_dsi_channels(2'b11);
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.SLAVES, abort_slave_count);
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DMOF, 1'b0);
			end
			
			#500us;
			// do a normal CRM at the end
			`create_and_send(spec_CRM_command_seq)
		end
	endtask
endclass