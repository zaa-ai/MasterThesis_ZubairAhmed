`include "svunit_defines.svh"

module dsi3_packets_test import project_pkg::*; ();
	import svunit_pkg::svunit_testcase;
	
	import spi_pkg::*;
	import common_pkg::*;
	import common_env_pkg::*;
	
	string name = "dsi3_packets_test";
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
	
		`SVTEST ("CRM_create_packet_test")
			for (logic[15:0] crc = 16'd0 ; crc < 16'd256; crc = crc + 16'd1) begin
				dsi3_crm_packet	packet = dsi3_crm_packet::create_packet({4'h9, 4'h3, 4'h9, 4'hc, 4'hc, 4'h8, crc[7:4], crc[3:0]});	
				
				`FAIL_UNLESS_EQUAL(packet.get_word(0),  16'h939c)
				`FAIL_UNLESS_EQUAL(packet.get_word(1),  {8'hc8, crc[7:0]})
				if (crc == 16'h00f2) begin
					`FAIL_UNLESS_EQUAL(packet.check_crc(),  1'b1)
				end
				else begin
					`FAIL_UNLESS_EQUAL(packet.check_crc(),  1'b0)
				end
			end
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("CRM_set_data_test")
			dsi3_crm_packet	packet = new();	
			packet.set_data({16'h939c, 16'hc8f2});
			
			`FAIL_UNLESS_EQUAL(packet.get_word(0),  16'h939c)
			`FAIL_UNLESS_EQUAL(packet.get_word(1),  16'hc8f2)
			`FAIL_UNLESS_EQUAL(packet.check_crc(),  1'b1)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("CRM_check_crc_test")
			dsi3_crm_packet	packet = new();	
			packet.set_data({16'h939c, 16'hc8f2});
			
			`FAIL_UNLESS_EQUAL(packet.get_word(0),  16'h939c)
			`FAIL_UNLESS_EQUAL(packet.get_word(1),  16'hc8f2)
			`FAIL_UNLESS_EQUAL(packet.check_crc(),  1'b1)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("PDCM_create_packet_16_test")
			for (logic[15:0] crc = 16'd0 ; crc < 16'd256; crc = crc + 16'd1) begin
				dsi3_pdcm_packet packet = dsi3_pdcm_packet::create_packet_16({16'h3b1f, {8'h20, crc[7:0]}}, dsi3_pkg::SID_8Bit);	
					
				`FAIL_UNLESS_EQUAL(packet.get_word(0),  16'h3b1f)
				`FAIL_UNLESS_EQUAL(packet.get_word(1),  {8'h20, crc[7:0]})
				if (crc == 16'h002e) begin
					`FAIL_UNLESS_EQUAL(packet.check_crc(),  1'b1)
				end
				else begin
					`FAIL_UNLESS_EQUAL(packet.check_crc(),  1'b0)
				end
			end
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("PDCM_check_crc_test")
			dsi3_pdcm_packet packet = new();
			convert_queue #(16, 4)::convert({16'h7f1c, 16'h90b0}, packet.data);
			packet.crc_correct = 1'b1;
			packet.source_id_symbols = dsi3_pkg::SID_8Bit;
			packet.update_crc();
				
			`FAIL_UNLESS_EQUAL(packet.get_word(0),  16'h7f1c)
			`FAIL_UNLESS_EQUAL(packet.get_word(1),  16'h90b0)
			`FAIL_UNLESS_EQUAL(packet.check_crc(), 1'b1)
		`SVTEST_END
		
		
		//=============================================================================
			
		// b4f0 885d 7fc4 ea67 0cdd dc0e c8e8
		`SVTEST ("PDCM_create_packet_test")
			dsi3_pdcm_packet packet = dsi3_pdcm_packet::create_packet_16({16'hb4f0, 16'h885d, 16'h7fc4, 16'hea67, 16'h0cdd, 16'hdc0e, 16'hc8e8}, dsi3_pkg::SID_8Bit);	
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::get_dsi3_seed(packet.data, dsi3_pkg::SID_8Bit), 8'hb4)
			`FAIL_UNLESS_EQUAL(packet.check_crc(),  1'b1)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("PDCM_random_packet_test")
			dsi3_pdcm_packet packet = new();
			
			`FAIL_IF_EQUAL(packet.randomize() with {data.size() == 11; crc_correct == 1'b1; source_id_symbols == dsi3_pkg::SID_8Bit;}, 0);
			
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::dsi3_calculate_correct_crc(packet.data, packet.source_id_symbols),  16'h0)
			`FAIL_UNLESS_EQUAL(packet.check_crc(), 1'b1)
		`SVTEST_END

		//=============================================================================
		
		`SVTEST ("PDCM_random_denso_packet_16_bit_crc_test")
			dsi3_pdcm_packet packet = new();
			
			`FAIL_IF_EQUAL(packet.randomize() with {data.size() == 8; crc_correct == 1'b1; source_id_symbols == dsi3_pkg::SID_16Bit_CRC; }, 0);
			
			`FAIL_UNLESS_EQUAL(packet.check_crc(), 1'b1)
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::dsi3_calculate_correct_crc(packet.data, packet.source_id_symbols),  16'h0)
		`SVTEST_END
			
		`SVTEST ("crc_calcuation_test_4_bit_seed")
			logic[3:0] data[$];
			logic[15:0] words[$] = {16'h4c01, 16'hce6a};
			
			`FAIL_UNLESS_EQUAL(convert_queue#(16, 4)::convert(words, data), 0)
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::dsi3_calculate_correct_crc(data, dsi3_pkg::SID_4Bit),  16'h0)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("crc_calcuation_test_8_bit_seed")
			logic[3:0] data[$];
			logic[15:0] words[$] = {16'h4c01, 16'hcea6};
			
			`FAIL_UNLESS_EQUAL(convert_queue#(16, 4)::convert(words, data), 0)
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::dsi3_calculate_correct_crc(data, dsi3_pkg::SID_8Bit),  16'h0)
		`SVTEST_END
		
		//=============================================================================
						
		`SVTEST ("crc_calcuation_test_ff_seed")
			logic[3:0] data[$];
			logic[15:0] words[$] = {16'h4c01, 16'hce0d};
			
			`FAIL_UNLESS_EQUAL(convert_queue#(16, 4)::convert(words, data), 0)
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::dsi3_calculate_correct_crc(data, dsi3_pkg::SID_0Bit),  16'h0)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("crc_calcuation_test")
			logic[3:0] data[$];
			logic[15:0] words[$] = {16'h219a, 16'h530f, 16'h1378, 16'h1e5a, 16'h1585, 16'h494a, 16'ha220, 16'he8a6, 16'h797b, 16'hc2c2, 16'h1013, 16'hab1b, 16'h1d93, 16'h429e};
			
			`FAIL_UNLESS_EQUAL(convert_queue#(16, 4)::convert(words, data), 0)
			`FAIL_UNLESS_EQUAL(crc_calculation_pkg::dsi3_calculate_correct_crc(data, dsi3_pkg::SID_0Bit),  16'h0)
		`SVTEST_END
		
		//=============================================================================
			
		`SVTEST ("pdcm_packet_crc_calculation_test")
			logic[15:0] words[$] = {16'h219a, 16'h530f, 16'h1378, 16'h1e5a, 16'h1585, 16'h494a, 16'ha220, 16'he8a6, 16'h797b, 16'hc2c2, 16'h1013, 16'hab1b, 16'h1d93, 16'h4200};
			dsi3_pdcm_packet packet = new();
			
			`FAIL_UNLESS_EQUAL(convert_queue#(16, 4)::convert(words, packet.data), 0)
			packet.crc_correct = 1'b1;
			packet.source_id_symbols = dsi3_pkg::SID_0Bit;
			packet.update_crc();
			
			`FAIL_UNLESS_EQUAL(packet.check_crc(), 1'b1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_16_bit_crc_test")
			logic[15:0] words[$] = {16'h3b1f, 16'h2092};
			logic[15:0] crc = crc_calculation_pkg::spi_calculate_correct_crc(words,crc_calculation_pkg::dsi3_crc_seed_16bit);
			dsi3_pdcm_packet packet_sid_0 = dsi3_pdcm_packet::create_packet_16({words, crc}, dsi3_pkg::SID_16Bit_CRC);
			`INFO($sformatf("16bit CRC = 0x%04h", crc));
			`FAIL_UNLESS_EQUAL(packet_sid_0.check_crc(),  1'b1)
		`SVTEST_END
		
		//=============================================================================
		
		`SVTEST ("pdcm_16_bit_crc_another_test")
			logic[15:0] words[$] = {16'h219a, 16'h530f, 16'h1378, 16'h1e5a, 16'h1585, 16'h494a, 16'ha220, 16'he8a6, 16'h797b, 16'hc2c2, 16'h1013, 16'hab1b, 16'h1d93, 16'h4200};
			logic[15:0] crc = crc_calculation_pkg::spi_calculate_correct_crc(words,crc_calculation_pkg::dsi3_crc_seed_16bit);
			dsi3_pdcm_packet packet_sid_0 = dsi3_pdcm_packet::create_packet_16({words, crc}, dsi3_pkg::SID_16Bit_CRC);
			`INFO($sformatf("16bit CRC = 0x%04h", crc));
			`FAIL_UNLESS_EQUAL(packet_sid_0.check_crc(),  1'b1)
		`SVTEST_END
		
		//=============================================================================

		`SVTEST ("pdcm_crc_examples_of_all_source_ids_test")
	
			dsi3_pdcm_packet packet_sid_0 = dsi3_pdcm_packet::create_packet_16({16'h3b1f, 16'h2092}, dsi3_pkg::SID_0Bit);
			dsi3_pdcm_packet packet_sid_1 = dsi3_pdcm_packet::create_packet_16({16'h3b1f, 16'h208f}, dsi3_pkg::SID_4Bit);
			dsi3_pdcm_packet packet_sid_2 = dsi3_pdcm_packet::create_packet_16({16'h3b1f, 16'h202e}, dsi3_pkg::SID_8Bit);
			
			`FAIL_UNLESS_EQUAL(packet_sid_0.check_crc(),  1'b1)
			`FAIL_UNLESS_EQUAL(packet_sid_1.check_crc(),  1'b1)
			`FAIL_UNLESS_EQUAL(packet_sid_2.check_crc(),  1'b1)
		`SVTEST_END
		
		
		//=============================================================================
		
		`SVTEST ("PDCM_check_crc_with_X_test")
			dsi3_pdcm_packet packet = new();
			convert_queue #(16, 4)::convert('{16'hbfe9, 16'hx18d}, packet.data);
			packet.source_id_symbols = dsi3_pkg::SID_8Bit;
			`FAIL_UNLESS_EQUAL(packet.check_crc(), 1'b0)
		`SVTEST_END
		
		`SVTEST ("PDCM_calculate_crc_with_X_test")
			logic[7:0] crc = crc_calculation_pkg::dsi3_crc('{4'hb, 4'hf, 4'he, 4'h9, 4'hx, 4'h1, 4'h8, 4'hd}, 8'hbf);
			`FAIL_UNLESS_EQUAL(crc,  8'hxx)
			
			crc = crc_calculation_pkg::dsi3_crc('{4'hb, 4'hf, 4'he, 4'h9, 4'h0, 4'h1, 4'h8, 4'hd}, 8'hbf);
			`FAIL_UNLESS_EQUAL(crc,  8'h95)
		`SVTEST_END
	
		
		// TODO: 16bit DSI CRC:
		// common_pkg::calculate_crc(..) mit einer convert_queue zu 16 und aufgefüllten Nullen ?!
			
	`SVUNIT_TESTS_END

endmodule
