class external_sync_crm_short_pulse_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(external_sync_crm_short_pulse_seq) 
	
	function new(string name = "");
		super.new("external_sync_crm_short_pulse");
	endfunction
	
	virtual task run_tests();
		log_sim_description("sync CRM using SYNCB pin and short pulses directly after CSB", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		set_syncb(1'b0);
		
		repeat(100) begin
			int delay = $urandom_range(1, 999);
			int pulse_width = $urandom_range(60, 110);
			transaction_recorder.clear_all();
			
			`spi_frame_begin
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(2500ns + delay * 1ns);
			
			set_syncb(1'b1);
			#(pulse_width * 1ns);
			set_syncb(1'b0);
			
			#500us;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				transaction_recorder.expect_tr_count(i, 1);
			end
		end
		transaction_recorder.disable_recorder();
	endtask
endclass