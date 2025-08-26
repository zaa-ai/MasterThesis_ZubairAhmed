`include "svunit_defines.svh"

module spi_protocol_listener_test import project_pkg::*; ();
	import svunit_pkg::svunit_testcase;
	
	import spi_pkg::*;
	
	string name = "spi_protocol_listener_test";
	svunit_testcase svunit_ut;
	
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
	
		`SVTEST ("create_spi_read_status_command")
			spi_read_status_seq status_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h0000, 16'h1234}, 
																{16'h8003, 16'hFFFF});
				
			`FAIL_UNLESS_EQUAL($cast(status_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(status_seq.get_word_count(), 1)
			
			`FAIL_UNLESS_EQUAL(status_seq.status.flags[CR0], 1)
			`FAIL_UNLESS_EQUAL(status_seq.status.flags[CR1], 1)
			
			`FAIL_UNLESS_EQUAL(status_seq.status.flags[HE],  1)
			`FAIL_UNLESS_EQUAL(status_seq.status.flags[BF],  0)
			`FAIL_UNLESS_EQUAL(status_seq.status.flags[SCI], 0)
			`FAIL_UNLESS_EQUAL(status_seq.status.flags[SPICRC], 0)
		`SVTEST_END
	
		//=============================================================================

		`SVTEST ("create_spi_tx_crc_request_command")
			spi_tx_crc_request_seq tx_crc_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h1000, 16'h1234}, 
																{16'h0000, 16'hAFFE});
				
			`FAIL_UNLESS_EQUAL($cast(tx_crc_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(tx_crc_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(tx_crc_seq.mosi_crc, 16'h1234)
			`FAIL_UNLESS_EQUAL(tx_crc_seq.miso_crc, 16'hAFFE)
		`SVTEST_END
			
		//=============================================================================
		
		`SVTEST ("create_spi_read_master_register_command")
			spi_read_master_register_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h2005, 16'h2000, 16'h1234}, 
																{16'h0000, 16'h2005, 16'hAFFE});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.address, 5)
			`FAIL_UNLESS_EQUAL(read_seq.data, 16'hAFFE)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses.size(), 0)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 2)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_read_master_register_command")
			spi_read_master_register_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h2005, 16'h1234}, 
																{16'h0000, 16'h2005});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.address, 5)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses.size(), 0)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 1)
		`SVTEST_END	
		
		//=============================================================================
	
		`SVTEST ("create_spi_read_master_register_burst_command")
			spi_read_master_register_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h2005, 16'h2006, 16'h2007, 16'h2008, 16'h2000, 16'h1234}, 
																{16'h0000, 16'h2005, 16'hA001, 16'hA002, 16'hA003, 16'hA004});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.address, 5)
			`FAIL_UNLESS_EQUAL(read_seq.data, 16'hA001)
			
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses.size(), 3)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[0], 12'h006)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[1], 12'h007)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[2], 12'h008)
			
			`FAIL_UNLESS_EQUAL(read_seq.burst_data.size(), 3)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[0], 16'hA002)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[1], 16'hA003)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[2], 16'hA004)
			
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 5)
		`SVTEST_END		
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_read_master_register_burst_command")
			spi_read_master_register_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h2005, 16'h2006, 16'h2007, 16'h2008, 16'h1234}, 
																{16'h0000, 16'h2005, 16'hA001, 16'hA002, 16'hA003});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.address, 5)
			`FAIL_UNLESS_EQUAL(read_seq.data, 16'hA001)
			
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses.size(), 3)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[0], 12'h006)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[1], 12'h007)
			`FAIL_UNLESS_EQUAL(read_seq.burst_addresses[2], 12'h008)
			
			`FAIL_UNLESS_EQUAL(read_seq.burst_data.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[0], 16'hA002)
			`FAIL_UNLESS_EQUAL(read_seq.burst_data[1], 16'hA003)
			
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("create_spi_read_crm_data_packets_first_channel")
			spi_read_crm_data_packets_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h3400, 16'h3000, 16'h3000, 16'h3000, 16'h1000, 16'h1234}, 
																{16'h0001, 16'h3400, 16'h1108, 16'h1234, 16'h5678, 16'hFFFF});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b01)

			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].channel_index, 2'd0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].symbol_count, 8'd8)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[0], 16'h1234)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[1], 16'h5678)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CE),  1'b1)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("create_spi_read_crm_data_packets_second_channel")
			spi_read_crm_data_packets_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h3800, 16'h3000, 16'h3000, 16'h3000, 16'h1000, 16'h1234}, 
																{16'h0000, 16'h3800, 16'h0008, 16'h1234, 16'h5678, 16'hFFFF});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b10)
	
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].channel_index, 2'd1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].symbol_count, 8'd8)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[0], 16'h1234)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[1], 16'h5678)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CRC), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CE),  1'b0)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("create_spi_read_crm_data_packets_of_both_channels")
			spi_read_crm_data_packets_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h3C00, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h3000, 16'h1000, 16'h1234}, 
																{16'h0000, 16'h3C00, 16'h5008, 16'h1234, 16'h5678, 16'h5008, 16'h9abc, 16'hdef0, 16'haaaa});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 7)
			`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b11)
	
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 2)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].channel_index, 2'd0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].symbol_count, 8'd8)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[0], 16'h1234)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[1], 16'h5678)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CE),  1'b0)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].channel_index, 2'd1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].symbol_count, 8'd8)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].data.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].data[0], 16'h9abc)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].data[1], 16'hdef0)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[1].get_value(CE),  1'b0)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_read_crm_data_1_word_channels")
			spi_read_crm_data_packets_seq read_seq;
			
			spi_seq seq = spi_protocol_listener::create_command({16'h3C00, 16'h1000, 16'h1234}, 
																{16'h0000, 16'h3C00, 16'haaaa});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete_word_count, 1)
			`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b11)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_read_crm_data_packets_one_of_both_channels")
			spi_read_crm_data_packets_seq read_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h3C00, 16'h3000, 16'h3000, 16'h3000, 16'h1000, 16'h1234}, 
																{16'h0000, 16'h3C00, 16'h5008, 16'h1234, 16'h5678, 16'haaaa});
		
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete_word_count, 4)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b11)
	
			`FAIL_UNLESS_EQUAL(read_seq.data_packets.size(), 1)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].channel_index, 2'd0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].symbol_count, 8'd8)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data.size(), 2)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[0], 16'h1234)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].data[1], 16'h5678)
			
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SCE), 1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CRC), 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(TE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(SE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(VE),  1'b0)
			`FAIL_UNLESS_EQUAL(read_seq.data_packets[0].get_value(CE),  1'b0)
		`SVTEST_END		
		
		//=============================================================================

		`SVTEST ("create_spi_write_master_register_command")
			spi_write_master_register_seq write_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h500F, 16'hAFFE, 16'h1234}, 
																{16'h0000, 16'hFFFF, 16'hFFFF});
		
			`FAIL_UNLESS_EQUAL($cast(write_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(write_seq.address, 12'h00F)
			`FAIL_UNLESS_EQUAL(write_seq.data, 16'hAFFE)
			`FAIL_UNLESS_EQUAL(write_seq.get_word_count(), 2)
		`SVTEST_END
			
		//=============================================================================
		
		`SVTEST ("create_spi_clear_dsi_command_queue_command")
			spi_clear_dsi_command_queue_seq clear_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h6800, 16'h1234}, 
																{16'h0000, 16'h6800});
				
			`FAIL_UNLESS_EQUAL($cast(clear_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(clear_seq.channel_bits, 2'b10)			
			`FAIL_UNLESS_EQUAL(clear_seq.get_word_count(), 1)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("create_spi_clear_dsi_data_buffers_command")
			spi_clear_dsi_data_buffers_seq clear_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h7C00, 16'h1234}, 
																{16'h0000, 16'h7C00});
				
			`FAIL_UNLESS_EQUAL($cast(clear_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(clear_seq.channel_bits, 2'b11)			
			`FAIL_UNLESS_EQUAL(clear_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(clear_seq.crm_buffer, 1'b0)
			`FAIL_UNLESS_EQUAL(clear_seq.pdcm_buffer, 1'b0)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_spi_clear_dsi_data_buffers_crm_and_pdcm_command")
			spi_clear_dsi_data_buffers_seq clear_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h7C03, 16'h1234}, 
																{16'h0000, 16'h7C03});
				
			`FAIL_UNLESS_EQUAL($cast(clear_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(clear_seq.channel_bits, 2'b11)			
			`FAIL_UNLESS_EQUAL(clear_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(clear_seq.crm_buffer, 1'b1)
			`FAIL_UNLESS_EQUAL(clear_seq.pdcm_buffer, 1'b1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_spi_clear_dsi_data_buffers_crm_command")
			spi_clear_dsi_data_buffers_seq clear_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h7C01, 16'h1234}, 
																{16'h0000, 16'h7C01});
				
			`FAIL_UNLESS_EQUAL($cast(clear_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(clear_seq.crm_buffer, 1'b1)
			`FAIL_UNLESS_EQUAL(clear_seq.pdcm_buffer, 1'b0)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_spi_clear_dsi_data_buffers_pdcm_command")
			spi_clear_dsi_data_buffers_seq clear_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h7C02, 16'h1234}, 
																{16'h0000, 16'h7C02});
				
			`FAIL_UNLESS_EQUAL($cast(clear_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(clear_seq.crm_buffer, 1'b0)
			`FAIL_UNLESS_EQUAL(clear_seq.pdcm_buffer, 1'b1)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("create_spi_crm_command")
			spi_crm_seq crm_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h8401, 16'h1234, 16'h5678, 16'h0000}, 
																{16'h0000, 16'h8401, 16'h1234, 16'h5678});
				
			`FAIL_UNLESS_EQUAL($cast(crm_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(crm_seq.channel_bits, 2'b01)		
			`FAIL_UNLESS_EQUAL(crm_seq.get_word_count(), 3)
			`FAIL_UNLESS_EQUAL(crm_seq.broad_cast, 1'b1)
			`FAIL_UNLESS_EQUAL(crm_seq.crm_packet.get_word(0), 16'h1234)
			`FAIL_UNLESS_EQUAL(crm_seq.crm_packet.get_word(1), 16'h5678)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("create_spi_crm_broad_cast_command")
			spi_crm_seq crm_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'h8800, 16'h1234, 16'h5678, 16'h0000}, 
																{16'h0000, 16'h8800, 16'h1234, 16'h5678});
				
			`FAIL_UNLESS_EQUAL($cast(crm_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(crm_seq.channel_bits, 2'b10)		
			`FAIL_UNLESS_EQUAL(crm_seq.get_word_count(), 3)
			`FAIL_UNLESS_EQUAL(crm_seq.broad_cast, 1'b0)
			`FAIL_UNLESS_EQUAL(crm_seq.crm_packet.get_word(0), 16'h1234)
			`FAIL_UNLESS_EQUAL(crm_seq.crm_packet.get_word(1), 16'h5678)
		`SVTEST_END	
		
		//=============================================================================

		`SVTEST ("create_spi_pdcm_command")
			spi_pdcm_seq pdcm_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hCC08}, 
																{16'h0000});
				
			`FAIL_UNLESS_EQUAL($cast(pdcm_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(pdcm_seq.channel_bits, 2'b11)		
			`FAIL_UNLESS_EQUAL(pdcm_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(pdcm_seq.pulse_count, 8)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("create_spi_read_pdcm_frame_seq")
			spi_read_pdcm_frame_seq read_seq;
			spi_dsi_data_packet data_packet;
			spi_seq seq;
			
			tdma_scheme_upload_listener::set_default_schemes();
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 8'h1b;
			
			seq = spi_protocol_listener::create_command({16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h1000, 16'h1234}, 
														{16'h0804, 16'h4400, 16'h0001, 16'h101b, 16'h915d, 16'hd50c, 16'h0595, 16'hd085, 16'h208c, 16'hf33e, 16'h0300, 16'haaaa});
				
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b01)		
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 10)
			
			data_packet = read_seq.get_data_packet(2'b0, 0);
			`FAIL_UNLESS_EQUAL(data_packet.symbol_count, 8'h1b)
			`FAIL_UNLESS_EQUAL(data_packet.data.size(), 7)
			`FAIL_UNLESS_EQUAL(data_packet.data[0], 16'h915d)
			`FAIL_UNLESS_EQUAL(data_packet.data[1], 16'hd50c)
			`FAIL_UNLESS_EQUAL(data_packet.data[2], 16'h0595)
			`FAIL_UNLESS_EQUAL(data_packet.data[3], 16'hd085)
			`FAIL_UNLESS_EQUAL(data_packet.data[4], 16'h208c)
			`FAIL_UNLESS_EQUAL(data_packet.data[5], 16'hf33e)
			`FAIL_UNLESS_EQUAL(data_packet.data[6], 16'h0300)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_read_pdcm_frame_1_word_seq")
			spi_read_pdcm_frame_seq read_seq;
			spi_seq seq;
			
			tdma_scheme_upload_listener::set_default_schemes();
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 8'h8;
			
			seq = spi_protocol_listener::create_command({16'h4C00, 16'h1000, 16'h1234}, 
														{16'h0000, 16'h4400, 16'haaaa});
				
			`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b11)		
			`FAIL_UNLESS_EQUAL(read_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(read_seq.incomplete_word_count, 1)
			`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), 1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_read_pdcm_frame_seq")
			spi_read_pdcm_frame_seq read_seq;
			spi_dsi_data_packet data_packet;
			spi_pdcm_frame_header frame_header;
			
			spi_seq seq;
			logic[15:0] data_in[$]  = {16'h4400, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000, 16'h4000};
			logic[15:0] data_out[$] = {16'h0804, 16'h4400, 16'h0001, 16'h101b, 16'h915d, 16'hd50c, 16'h0595, 16'hd085, 16'h208c, 16'hf33e};
			
			tdma_scheme_upload_listener::set_default_schemes();
			tdma_scheme_upload_listener::schemes[0].valid = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].enable = 1'b1;
			tdma_scheme_upload_listener::schemes[0].packets[0].symbol_count = 8'h1b;
			
			for(int word_count = 1; word_count < data_in.size(); word_count++) begin
				logic[15:0] temp_data_in[$];
				logic[15:0] temp_data_out[$];
				
				`INFO($sformatf("incomplete read PDCM with %0d words", word_count));
				
				for(int i = 0; i < word_count; i++) begin
					temp_data_in.push_back(data_in[i]);
					temp_data_out.push_back(data_out[i]);
				end
				
				temp_data_in.push_back(16'h1000);
				temp_data_in.push_back(16'h1234);
				temp_data_out.push_back(16'h0300);
				temp_data_out.push_back(16'haaaa);
				
				seq = spi_protocol_listener::create_command(temp_data_in, temp_data_out);
					
				`FAIL_UNLESS_EQUAL($cast(read_seq, seq), 1)
				`FAIL_UNLESS_EQUAL(read_seq.channel_bits, 2'b01)		
				`FAIL_UNLESS_EQUAL(read_seq.get_word_count(), word_count)
				
				if(word_count >= 3) begin
					frame_header = read_seq.get_frame_header(2'b0);
					`FAIL_UNLESS_EQUAL(frame_header.packet_count, 8'd1)
					if(word_count >= 4) begin
						data_packet = read_seq.get_data_packet(2'b0, 0);
						`FAIL_UNLESS_EQUAL(data_packet.symbol_count, 8'h1b)
						if(word_count >= 5) begin
							for(int data_index = 0; data_index < word_count - 4; data_index++) begin
								`FAIL_UNLESS_EQUAL(data_packet.data[data_index], temp_data_out[4 + data_index])
							end
						end
					end
				end
			end
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_spi_dsi_wait_command")
			spi_dsi_wait_seq wait_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hD400, 16'h0123}, 
																{16'h0000, 16'hD400});
				
			`FAIL_UNLESS_EQUAL($cast(wait_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(wait_seq.channel_bits, 2'b01)		
			`FAIL_UNLESS_EQUAL(wait_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(wait_seq.wait_time, 15'h123)
		`SVTEST_END	
		
		//=============================================================================

		`SVTEST ("create_spi_dsi_wait_command_filler_test")
			spi_dsi_wait_seq wait_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hDCFF, 16'h8500}, 
																{16'h0000, 16'hDCFF});
				
			`FAIL_UNLESS_EQUAL($cast(wait_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(wait_seq.channel_bits, 2'b11)		
			`FAIL_UNLESS_EQUAL(wait_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(wait_seq.wait_time, 15'h500)
			`FAIL_UNLESS_EQUAL(wait_seq.get_word(0), 16'hDCFF)
			`FAIL_UNLESS_EQUAL(wait_seq.get_word(1), 16'h8500)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("create_spi_sync_dsi_channels_intern_command")
			spi_sync_dsi_channels_seq sync_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hEC00}, 
																{16'h0000});
				
			`FAIL_UNLESS_EQUAL($cast(sync_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(sync_seq.channel_bits, 2'b11)		
			`FAIL_UNLESS_EQUAL(sync_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(sync_seq.external_sync, 1'b0)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("create_spi_sync_dsi_channels_extern_command")
			spi_sync_dsi_channels_seq sync_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hEC01}, 
																{16'h0000});
				
			`FAIL_UNLESS_EQUAL($cast(sync_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(sync_seq.channel_bits, 2'b11)		
			`FAIL_UNLESS_EQUAL(sync_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(sync_seq.external_sync, 1'b1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_spi_upload_tdma_packet_index_zero_command")
			spi_upload_tdma_packet_seq upload_packet_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hb420, 16'h001e, 16'h0046, 16'hC004}, 
																{16'h0000, 16'hb420, 16'h001e, 16'h0046});
				
			`FAIL_UNLESS_EQUAL($cast(upload_packet_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.channel_bits, 2'b01)		
			`FAIL_UNLESS_EQUAL(upload_packet_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.packet_index, 4'd0)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.earliest_start_time, 16'h1e)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.latest_start_time, 16'h46)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.id_symbol_count, 2'b11)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.symbol_count, 4)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("create_spi_upload_tdma_packet_command")
			spi_upload_tdma_packet_seq upload_packet_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hbc21, 16'h001e, 16'h0046, 16'h8008}, 
																{16'h0000, 16'hbc21, 16'h001e, 16'h0046});
				
			`FAIL_UNLESS_EQUAL($cast(upload_packet_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.channel_bits, 2'b11)		
			`FAIL_UNLESS_EQUAL(upload_packet_seq.get_word_count(), 4)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.packet_index, 4'd1)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.earliest_start_time, 16'h1e)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.latest_start_time, 16'h46)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.id_symbol_count, 2'b10)
			`FAIL_UNLESS_EQUAL(upload_packet_seq.tdma_packet.symbol_count, 8)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_spi_start_discovery_mode_command")
			spi_discovery_mode_seq disc_seq;
		
			spi_seq seq = spi_protocol_listener::create_command({16'hAC00, 16'h1234, 16'h5678, 16'h9ABC}, 
																{16'h0000, 16'hAC00, 16'h1234, 16'h5678});
			
			`FAIL_UNLESS_EQUAL($cast(disc_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(disc_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(disc_seq.channel_bits, 2'b11)
		`SVTEST_END	
		
		//=============================================================================
			
		`SVTEST ("create_compare_mask_test")
			`FAIL_UNLESS_EQUAL(spi_protocol_listener::create_compare_mask(16), 16'hffff)
			`FAIL_UNLESS_EQUAL(spi_protocol_listener::create_compare_mask(15), 16'hfffe)
			`FAIL_UNLESS_EQUAL(spi_protocol_listener::create_compare_mask(2), 16'hc000)
			`FAIL_UNLESS_EQUAL(spi_protocol_listener::create_compare_mask(1), 16'h8000)
			`FAIL_UNLESS_EQUAL(spi_protocol_listener::create_compare_mask(0), 16'h0000)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("create_spi_upload_tdma_scheme_test")
			spi_upload_tdma_packet_seq upload_seq;
			
			spi_seq seq = spi_protocol_listener::create_command({16'hbc20, 16'h001e, 16'h0046, 16'h8008}, 
																{16'h0000, 16'hbc20, 16'h001e, 16'h0046});
			
			`FAIL_UNLESS_EQUAL($cast(upload_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(upload_seq.channel_bits, 2'b11)
			`FAIL_UNLESS_EQUAL(upload_seq.packet_index, 0)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.earliest_start_time, 30)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.latest_start_time, 70)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.symbol_count, 8)
			`FAIL_UNLESS_EQUAL(upload_seq.tdma_packet.id_symbol_count, 2)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_spi_validate_tdma_scheme_test")
			spi_validate_tdma_scheme_seq validate_seq;
			
			spi_seq seq = spi_protocol_listener::create_command({16'hbcc1, 16'h012c}, 
																{16'h0000, 16'hbcc1});
			
			`FAIL_UNLESS_EQUAL($cast(validate_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(validate_seq.channel_bits, 2'b11)
			`FAIL_UNLESS_EQUAL(validate_seq.packet_count, 1)
			`FAIL_UNLESS_EQUAL(validate_seq.pdcm_period, 300)
		`SVTEST_END	
		
		//=============================================================================

		`SVTEST ("create_spi_reset_command_0")
			spi_reset_seq reset_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFE}, 
																{16'h0000, 16'hFFFF, 16'hFFFF, 16'hFFFF});
				
			`FAIL_UNLESS_EQUAL($cast(reset_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b0)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word_count(), 4)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("create_spi_reset_command_1")
			spi_reset_seq reset_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF}, 
																{16'h0000, 16'hFFFF, 16'hFFFF, 16'hFFFF});
				
			`FAIL_UNLESS_EQUAL($cast(reset_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b0)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word_count(), 4)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_reset_command_1")
			spi_reset_seq reset_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hFFFF, 16'h1234}, 
																{16'h0000, 16'hFFFF});
		
			`FAIL_UNLESS_EQUAL($cast(reset_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word_count(), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete_word_count, 1)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_reset_command_2")
			spi_reset_seq reset_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hFFFF, 16'hFFFF, 16'h1234}, 
																{16'h0000, 16'hFFFF, 16'hFFFF});
		
			`FAIL_UNLESS_EQUAL($cast(reset_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word_count(), 2)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete_word_count, 2)
		`SVTEST_END	
		
		//=============================================================================
		
		`SVTEST ("create_incomplete_spi_reset_command_3")
			spi_reset_seq reset_seq;
			spi_seq seq = spi_protocol_listener::create_command({16'hFFFF, 16'hFFFF, 16'hFFFF, 16'h1234}, 
																{16'h0000, 16'hFFFF, 16'hFFFF, 16'hFFFF});
		
			`FAIL_UNLESS_EQUAL($cast(reset_seq, seq), 1)
			`FAIL_UNLESS_EQUAL(reset_seq.get_word_count(), 3)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete, 1'b1)
			`FAIL_UNLESS_EQUAL(reset_seq.incomplete_word_count, 3)
		`SVTEST_END	
			
	`SVUNIT_TESTS_END

endmodule
