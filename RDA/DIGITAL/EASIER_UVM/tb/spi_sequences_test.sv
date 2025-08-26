`include "svunit_defines.svh"

module spi_sequences_test import project_pkg::*; ();
	import svunit_pkg::svunit_testcase;
	
	import spi_pkg::*;
	
	string name = "spi_sequences_test";
	svunit_testcase svunit_ut;
	logic[15:0] word;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	
	//===================================
	// Build
	//===================================
	function void build();
		svunit_ut = new(name);
	endfunction

	//===================================
	// Setup for running the Unit Tests
	//===================================
	task setup();
		svunit_ut.setup();
		/* Place Setup Code Here */
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
		/* Place Teardown Code Here */
	endtask
	
	
	//===================================
	// All tests are defined between the
	// SVUNIT_TESTS_BEGIN/END macros
	//
	// Each individual test must be
	// defined between `SVTEST(_NAME_)
	// `SVTEST_END
	//
	// i.e.
	//	 `SVTEST(mytest)
	//		 <test code>
	//	 `SVTEST_END
	//===================================
	`SVUNIT_TESTS_BEGIN
	
		`SVTEST ("spi_read_status_sequence")
			spi_read_status_seq status_seq = new();
			
			`FAIL_IF_EQUAL(status_seq.randomize(), 0)
			`FAIL_UNLESS_EQUAL(status_seq.get_word_count(), 1)
			word = status_seq.get_word(0); 
			`FAIL_UNLESS_EQUAL(word[15:12], 4'h0)
		`SVTEST_END
		
		//=============================================================================
	
		`SVTEST ("spi_reset_last_0_sequence")
			spi_reset_seq reset_seq = new();
			
			`FAIL_IF_EQUAL(reset_seq.randomize()with { last_bit == 1'b0;}, 0);
			
			`FAIL_UNLESS_EQUAL(reset_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(0), 16'hFFFF)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(1), 16'hFFFF)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(2), 16'hFFFF)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(3), 16'hFFFE)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_reset_last_1_sequence")
			spi_reset_seq reset_seq = new();
			
			`FAIL_IF_EQUAL(reset_seq.randomize()with { last_bit == 1'b1;}, 0);
			
			`FAIL_UNLESS_EQUAL(reset_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(0), 16'hFFFF)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(1), 16'hFFFF)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(2), 16'hFFFF)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word(3), 16'hFFFF)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_tx_crc_request_sequence")
			spi_tx_crc_request_seq tx_crc_seq = new();
			
			`FAIL_IF_EQUAL(tx_crc_seq.randomize() with { mosi_crc == 16'hAFFE;}, 0)
			
			`FAIL_UNLESS_EQUAL(tx_crc_seq.get_word_count(), 2)
			word = tx_crc_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'h1)
			`FAIL_UNLESS_EQUAL(tx_crc_seq.get_word(1), 16'hAFFE)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("spi_read_master_register_sequence")
			spi_read_master_register_seq read_seq = new();
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {address == 12'h005; burst_addresses.size() == 0;}, 0)
		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(0), 16'h2005)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(1), 16'h2000)
		`SVTEST_END			
		
		//=============================================================================
	
		`SVTEST ("spi_read_master_register_burst_sequence")
			spi_read_master_register_seq read_seq = new();
		
			`FAIL_IF_EQUAL(read_seq.randomize() with {	address == 12'h005; 
										burst_addresses.size() == 3; 
										burst_addresses[0] == 12'h006; 
										burst_addresses[1] == 12'h007; 
										burst_addresses[2] == 12'h008;}, 0)
		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 5)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(0), 16'h2005)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(1), 16'h2006)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(2), 16'h2007)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(3), 16'h2008)
			`FAIL_UNLESS_EQUAL(read_seq.get_word(4), 16'h2000)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("spi_read_crm_data_packets_first_channel_sequence")
			spi_read_crm_data_packets_seq read_seq = new();
			logic[15:0] word_0, word_1, word_2, word_3;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b01;}, 0) 
		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			word_0 = read_seq.get_word(0);
			word_1 = read_seq.get_word(1);
			word_2 = read_seq.get_word(2);
			word_3 = read_seq.get_word(3);

			`FAIL_UNLESS_EQUAL(word_0[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_0[11], 1'b0)
			`FAIL_UNLESS_EQUAL(word_0[10], 1'b1)
			`FAIL_UNLESS_EQUAL(word_1[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_2[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_3[15:12], 4'h3)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("spi_read_crm_data_packets_second_channel_sequence")
			spi_read_crm_data_packets_seq read_seq = new();
			logic[15:0] word_0, word_1, word_2, word_3;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b10;}, 0) 
		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			word_0 = read_seq.get_word(0);
			word_1 = read_seq.get_word(1);
			word_2 = read_seq.get_word(2);
			word_3 = read_seq.get_word(3);
			
			`FAIL_UNLESS_EQUAL(word_0[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_0[11], 1'b1)
			`FAIL_UNLESS_EQUAL(word_0[10], 1'b0)
			
			`FAIL_UNLESS_EQUAL(word_1[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_2[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_3[15:12], 4'h3)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("spi_read_crm_data_packets_both_channels_sequence")
			spi_read_crm_data_packets_seq read_seq = new();
			logic[15:0] word_0, word_1, word_2, word_3, word_4, word_5, word_6;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b11;}, 0) 
		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 7)
			word_0 = read_seq.get_word(0);
			word_1 = read_seq.get_word(1);
			word_2 = read_seq.get_word(2);
			word_3 = read_seq.get_word(3);
			word_4 = read_seq.get_word(4);
			word_5 = read_seq.get_word(5);
			word_6 = read_seq.get_word(6);
			
			`FAIL_UNLESS_EQUAL(word_0[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_0[11], 1'b1)
			`FAIL_UNLESS_EQUAL(word_0[10], 1'b1)
			
			`FAIL_UNLESS_EQUAL(word_1[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_2[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_3[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_4[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_5[15:12], 4'h3)
			`FAIL_UNLESS_EQUAL(word_6[15:12], 4'h3)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("spi_read_crm_data_packets_repeat_fill_sequence")
			spi_read_crm_data_packets_seq read_seq = new();
			logic[15:0] word_1, word_2, word_3;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b10;}, 0) 
		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			
			word_1 = read_seq.get_word(1);
			word_2 = read_seq.get_word(2);
			word_3 = read_seq.get_word(3);
			
			repeat(10) begin
				`FAIL_UNLESS_EQUAL(read_seq.get_word(1), word_1)
				`FAIL_UNLESS_EQUAL(read_seq.get_word(2), word_2)
				`FAIL_UNLESS_EQUAL(read_seq.get_word(3), word_3)
			end
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("spi_write_master_register_sequence")
			spi_write_master_register_seq write_seq = new();
			
			`FAIL_IF_EQUAL(write_seq.randomize() with {address == 12'h00F; data == 16'hAFFE;}, 0)
			
			`FAIL_UNLESS_EQUAL(write_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(write_seq.get_word(0), 16'h500F)
			`FAIL_UNLESS_EQUAL(write_seq.get_word(1), 16'hAFFE)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("spi_clear_dsi_command_queue_sequence")
			spi_clear_dsi_command_queue_seq clear_seq = new(); 
				
			`FAIL_IF_EQUAL(clear_seq.randomize() with {channel_bits == 2'b01;}, 0)
			
			`FAIL_UNLESS_EQUAL(clear_seq.get_word_count(), 1)
			word = clear_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'h6)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b01)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("spi_clear_dsi_data_buffers_crm_only_sequence")
			spi_clear_dsi_data_buffers_seq clear_seq = new();
			
			`FAIL_IF_EQUAL(clear_seq.randomize() with {channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b0;}, 0)
			
			`FAIL_UNLESS_EQUAL(clear_seq.get_word_count(), 1)
			word = clear_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'h7)
			`FAIL_UNLESS_EQUAL(word[11:10],  2'b11)
			`FAIL_UNLESS_EQUAL(word[1],  1'b0)
			`FAIL_UNLESS_EQUAL(word[0],  1'b1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_clear_dsi_data_buffers_pdcm_only_sequence")
			spi_clear_dsi_data_buffers_seq clear_seq = new();
			
			`FAIL_IF_EQUAL(clear_seq.randomize() with {channel_bits == 2'b11; crm_buffer == 1'b0; pdcm_buffer == 1'b1;}, 0)
			
			`FAIL_UNLESS_EQUAL(clear_seq.get_word_count(), 1)
			word = clear_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'h7)
			`FAIL_UNLESS_EQUAL(word[11:10],  2'b11)
			`FAIL_UNLESS_EQUAL(word[1],  1'b1)
			`FAIL_UNLESS_EQUAL(word[0],  1'b0)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("spi_crm_sequence")
			spi_crm_seq crm_seq = new();
			
			`FAIL_IF_EQUAL(crm_seq.randomize() with {channel_bits == 2'b11; broad_cast == 1'b0;}, 0)
			crm_seq.crm_packet.set_data({16'h1234, 16'h5678});
			
			`FAIL_UNLESS_EQUAL(crm_seq.get_word_count(), 3)
			word = crm_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'h8)
			`FAIL_UNLESS_EQUAL(word[11:10],  2'b11)
			`FAIL_UNLESS_EQUAL(crm_seq.get_word(1), 16'h1234)
			`FAIL_UNLESS_EQUAL(crm_seq.get_word(2), 16'h5678)
			
			// word at index 0 must not be changed by subsequent calls of get_word(x)
			repeat(10) begin
				`FAIL_UNLESS_EQUAL(crm_seq.get_word(0), word)
			end
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("spi_crm_broad_cast_sequence")
			spi_crm_seq crm_seq = new();
				
			`FAIL_IF_EQUAL(crm_seq.randomize() with {channel_bits == 2'b11; broad_cast == 1'b1;}, 0)
			crm_seq.crm_packet.set_data({16'h1234, 16'h5678});	
			
			`FAIL_UNLESS_EQUAL(crm_seq.get_word_count(), 3)
			word = crm_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'h8)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
			`FAIL_UNLESS_EQUAL(word[0],     1'b1)
			`FAIL_UNLESS_EQUAL(crm_seq.get_word(1), 16'h1234)
			`FAIL_UNLESS_EQUAL(crm_seq.get_word(2), 16'h5678)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("spi_pdcm_sequence")
			spi_pdcm_seq pdcm_seq = new();
			
			`FAIL_IF_EQUAL(pdcm_seq.randomize() with {channel_bits == 2'b11; pulse_count == 8;}, 0)
			
			`FAIL_UNLESS_EQUAL(pdcm_seq.get_word_count(), 1)
			word = pdcm_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'hC)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
			`FAIL_UNLESS_EQUAL(word[5:0], 6'h8)
		`SVTEST_END		
		
		//=============================================================================
			
		`SVTEST ("spi_dsi_wait_sequence")
			spi_dsi_wait_seq wait_seq = new();
			
			`FAIL_IF_EQUAL(wait_seq.randomize() with {channel_bits == 2'b01; wait_time == 15'h123;}, 0)
			
			`FAIL_UNLESS_EQUAL(wait_seq.get_word_count(), 2)
			word = wait_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'hD)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b01)
			word = wait_seq.get_word(1);
			`FAIL_UNLESS_EQUAL(word[14:0], 15'h123)
		`SVTEST_END			
			
		//=============================================================================
			
		`SVTEST ("spi_sync_dsi_channels_intern_sequence")
			spi_sync_dsi_channels_seq sync_seq = new();
				
			`FAIL_IF_EQUAL(sync_seq.randomize() with {channel_bits == 2'b11; external_sync == 1'b0;}, 0)
			
			`FAIL_UNLESS_EQUAL(sync_seq.get_word_count(), 1)
			word = sync_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'hE)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
		`SVTEST_END				
		
		//=============================================================================
			
		`SVTEST ("spi_sync_dsi_channels_extern_sequence")
			spi_sync_dsi_channels_seq sync_seq = new();
				
			`FAIL_IF_EQUAL(sync_seq.randomize() with {channel_bits == 2'b11; external_sync == 1'b1;}, 0)
			
			`FAIL_UNLESS_EQUAL(sync_seq.get_word_count(), 1)
			word = sync_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'hE)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
			`FAIL_UNLESS_EQUAL(word[0],     1'b1)
		`SVTEST_END		
		
		//=============================================================================
			
		`SVTEST ("spi_start_discovery_mode_sequence")
			spi_discovery_mode_seq discovery_seq = new();
			
			`FAIL_IF_EQUAL(discovery_seq.randomize() with {channel_bits == 2'b11;}, 0)
			
			`FAIL_UNLESS_EQUAL(discovery_seq.get_word_count(), 1)
			word = discovery_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'hA)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_upload_tdma_packet_sequence")
			spi_upload_tdma_packet_seq tdma_seq = new();
				
			`FAIL_IF_EQUAL(tdma_seq.randomize() with {
					channel_bits == 2'b11; 
					packet_index == 4'd1; 
					tdma_packet.earliest_start_time == 16'd120; 
					tdma_packet.latest_start_time == 16'd240;
					tdma_packet.id_symbol_count == 2'b00;
					tdma_packet.symbol_count == 16;}, 0)
			
			`FAIL_UNLESS_EQUAL(tdma_seq.get_word_count(), 4)
			word = tdma_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'hB)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
			`FAIL_UNLESS_EQUAL(word[5],   	1'b1)
			`FAIL_UNLESS_EQUAL(word[3:0],   4'b1)
			`FAIL_UNLESS_EQUAL(tdma_seq.get_word(1), 16'd120)
			`FAIL_UNLESS_EQUAL(tdma_seq.get_word(2), 16'd240)
			word = tdma_seq.get_word(3);
			`FAIL_UNLESS_EQUAL(word[15:14], 2'b00)
			`FAIL_UNLESS_EQUAL(word[7:0], 8'd16)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("spi_validate_tdma_scheme_seq")
			spi_validate_tdma_scheme_seq tdma_seq = new();
			
			`FAIL_IF_EQUAL(tdma_seq.randomize() with {channel_bits == 2'b10; packet_count == 4'd3; pdcm_period == 16'd500;}, 0)
			
			`FAIL_UNLESS_EQUAL(tdma_seq.get_word_count(), 2)
			word = tdma_seq.get_word(0);
			`FAIL_UNLESS_EQUAL(word[15:12], 4'hB)
			`FAIL_UNLESS_EQUAL(word[11:10], 2'b10)
			`FAIL_UNLESS_EQUAL(word[5],   	1'b0)
			`FAIL_UNLESS_EQUAL(word[3:0],   4'h3)
			
			word = tdma_seq.get_word(1);
			`FAIL_UNLESS_EQUAL(word,   16'd500)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_frame_test")
			spi_read_pdcm_frame_seq read_seq = new();
			
			tdma_scheme_upload_listener::set_default_schemes();
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 8'h1b;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b01;}, 0) 
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 10)
			
			for (int i = 0; i < 10; i++) begin
				logic[15:0] word = read_seq.get_word(i);	
				`FAIL_UNLESS_EQUAL(word[15:12], 4'h4)
				if(i==0) begin
					`FAIL_UNLESS_EQUAL(word[11:10], 2'b01)
				end
			end
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("spi_read_pdcm_frame_repeat_fill_sequence")
			spi_read_pdcm_frame_seq read_seq = new();
			logic[15:0] words[7:0];
			
			tdma_scheme_upload_listener::set_default_schemes();
			
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 8;
			tdma_scheme_upload_listener::schemes[0].packets[1].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[1].symbol_count = 8;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b01;}, 0) 
		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 8)
			
			for (int i = 0; i < 8; i++) begin
				words[i] = read_seq.get_word(i);
				`FAIL_UNLESS_EQUAL(words[i][15:12], 4'h4)
				if(i==0) begin
					`FAIL_UNLESS_EQUAL(words[i][11:10], 2'b01)
				end
			end
			repeat(10) begin
				for (int i = 0; i < 8; i++) begin
					`FAIL_UNLESS_EQUAL(read_seq.get_word(i), words[i]);
				end
			end
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("spi_read_pdcm_frame_without_tdma_scheme_both_channels")
			spi_read_pdcm_frame_seq read_seq = new();
			
			tdma_scheme_upload_listener::set_default_schemes();
			tdma_scheme_upload_listener::schemes[0].valid = 1'b0;
			tdma_scheme_upload_listener::schemes[1].valid = 1'b0;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b11;}, 0) 
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 3)
			
			for (int i = 0; i < 3; i++) begin
				logic[15:0] word = read_seq.get_word(i);
				`FAIL_UNLESS_EQUAL(word[15:12], 4'h4)
				if(i==0) begin
					`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
				end
			end
		`SVTEST_END			
		
		//=============================================================================

		`SVTEST ("spi_read_pdcm_frame_without_tdma_scheme_single_channel")
			spi_read_pdcm_frame_seq read_seq = new();
			
			tdma_scheme_upload_listener::set_default_schemes();
			tdma_scheme_upload_listener::schemes[0].valid = 1'b0;
			tdma_scheme_upload_listener::schemes[1].valid = 1'b0;
			
			`FAIL_IF_EQUAL(read_seq.randomize() with {channel_bits == 2'b10;}, 0) 
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 2)
			
			for (int i = 0; i < 2; i++) begin
				logic[15:0] word = read_seq.get_word(i);
				`FAIL_UNLESS_EQUAL(word[15:12], 4'h4)
				if(i==0) begin
					`FAIL_UNLESS_EQUAL(word[11:10], 2'b10)
				end
			end
		`SVTEST_END	
		
		//=============================================================================
		
	`SVTEST ("spi_measure_quiescent_current_sequence")
		spi_measure_quiescent_current_seq discovery_seq = new();
		
		`FAIL_IF_EQUAL(discovery_seq.randomize() with {channel_bits == 2'b11;}, 0)
		
		`FAIL_UNLESS_EQUAL(discovery_seq.get_word_count(), 1)
		word = discovery_seq.get_word(0);
		`FAIL_UNLESS_EQUAL(word[15:12], 4'h9)
		`FAIL_UNLESS_EQUAL(word[11:10], 2'b11)
	`SVTEST_END
			
	`SVUNIT_TESTS_END

endmodule
