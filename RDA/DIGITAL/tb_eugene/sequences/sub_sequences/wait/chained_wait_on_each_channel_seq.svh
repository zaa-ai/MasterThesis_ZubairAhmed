class chained_wait_on_each_channel_seq extends base_wait_seq;
	
	`uvm_object_utils(chained_wait_on_each_channel_seq) 
    
	function new(string name = "");
		super.new("chained_wait_on_each_channel");
	endfunction : new

	virtual task run_tests();
		log_sim_description("perform multiple DSI wait commands in a row on each channel", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		create_CRM_packets_without_data();
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			spi_dsi_wait_seq wait1_seq, wait2_seq, wait3_seq;
			int wait_sum;
			time start;
			
			transaction_recorder.clear_all();
			`spi_frame_begin
				`spi_frame_send(wait1_seq, channel_bits == 2'b01 << channel; wait_time inside {[15'd500:15'd1500]};)
				`spi_frame_send(wait2_seq, channel_bits == 2'b01 << channel; wait_time inside {[15'd500:15'd1500]};)
				`spi_frame_send(wait3_seq, channel_bits == 2'b01 << channel; wait_time inside {[15'd500:15'd1500]};)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			start = $time;
			#300us;
			transaction_recorder.expect_tr_count(channel, 0);
			
			wait_sum = int'(wait1_seq.wait_time + wait2_seq.wait_time + wait3_seq.wait_time);
			log_sim_description($sformatf("perform chained DSI wait (%0d + %0d + %0d = %0d) on channel %0d", wait1_seq.wait_time, wait2_seq.wait_time, wait3_seq.wait_time, wait_sum, channel), LOG_LEVEL_OTHERS);
			#(wait_sum * 1us);
			
			expect_wait_time_for_all_channels(0);
			transaction_recorder.expect_tr_count(channel, 1);
			compare_times(wait_sum * 1us, transaction_recorder.get_master_tr_begin_time(channel, 0) - start, $sformatf("DSI wait time at channel %0d", channel), 15us);
		end
		transaction_recorder.disable_recorder();
	endtask
endclass

