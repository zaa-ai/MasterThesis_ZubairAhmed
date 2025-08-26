`include "uvm_macros.svh"
`include "svunit_defines.svh"

module otp_writer_test;
	import svunit_pkg::svunit_testcase;
	import common_env_pkg::*;
	
	string name = "otp_writer_test";
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
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
	endtask
		
	function automatic otp_entry entry(logic[15:0] word);
		ecc_word_otp_entry ecc_entry = new();	
		if(ecc_entry.randomize() with {value == word;} == 0) `ERROR("failed to randomize");
		return ecc_entry;
	endfunction
		
	function automatic void read_otp(string file_name, int size, ref logic[11:0] data[$]);
		int position = 0;
		int file = $fopen(file_name, "r");
				
		while (!$feof(file) && position < size) begin 
			logic [11:0] next_data;
			$fscanf(file,"%3h\n", next_data); 
			data.push_back(next_data);
			position++;
		end
		
		$fclose(file);
	endfunction
	
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
	
		`SVTEST ("empty_otp_test")
			otp_writer writer = new();
			writer.write("otp.dat");
			
			begin
				logic[11:0] data[$] = {};
				read_otp("otp.dat", 4096, data);
				for (int i=0;  i< 4096; i++) begin
					`FAIL_UNLESS_EQUAL(data[i], 12'h000)
				end
			end
		`SVTEST_END
			
		`SVTEST ("basic_otp_test")
			otp_writer writer = new();
			for (int counter=0; counter<32; counter++) begin
				basic_otp_entry entry = new(counter);
				writer.add_entry(entry);
			end
			writer.write("otp_basic.dat");
			
			begin
				logic[11:0] data[$] = {};
				read_otp("otp_basic.dat", 4096, data);
				for (int i=0;  i< 4096; i++) begin
					if(i < 32) begin
						`FAIL_UNLESS_EQUAL(data[i], 12'(i));
					end
					else begin
						`FAIL_UNLESS_EQUAL(data[i], 12'h000);
					end
				end
			end
		`SVTEST_END
			
		`SVTEST ("ecc_otp_entry_test")
			otp_entry e = entry(16'h9000);
			`FAIL_UNLESS_EQUAL(2, e.get_value_count());
			`FAIL_UNLESS_EQUAL(12'h190, e.get_value(0, 0));
			`FAIL_UNLESS_EQUAL(12'h200, e.get_value(1, 1));
		`SVTEST_END
		
		`SVTEST ("ecc_otp_entry_2_test")
			otp_entry e = entry(16'h800);
			`FAIL_UNLESS_EQUAL(2, e.get_value_count());
			`FAIL_UNLESS_EQUAL(12'h208, e.get_value(0, 0));
			`FAIL_UNLESS_EQUAL(12'h500, e.get_value(1, 1));
		`SVTEST_END
			
		`SVTEST ("ecc_otp_test")
			otp_writer writer = new();
			writer.add_entry(entry(16'h9000));
			writer.add_entry(entry(16'haffe));
			writer.add_entry(entry(16'h9001));
			writer.add_entry(entry(16'hd00f));
			writer.write("otp_ecc.dat");
			
			begin
				logic[11:0] data[$] = {};
				read_otp("otp_ecc.dat", 8, data);
				
				`FAIL_UNLESS_EQUAL(data[0], 12'h190);
				`FAIL_UNLESS_EQUAL(data[1], 12'h200);
				`FAIL_UNLESS_EQUAL(data[2], 12'hdaf);
				`FAIL_UNLESS_EQUAL(data[3], 12'h2fe);
				`FAIL_UNLESS_EQUAL(data[4], 12'hc90);
				`FAIL_UNLESS_EQUAL(data[5], 12'hf01);
				`FAIL_UNLESS_EQUAL(data[6], 12'h3d0);
				`FAIL_UNLESS_EQUAL(data[7], 12'h80f);
			end
		`SVTEST_END
			
		`SVTEST ("ecc_otp_writer_test")
			ecc_otp_writer writer = new();
			writer.add_address_data(16'h9000, 16'haffe);
			writer.add_address_data(16'h9001, 16'hd00f);
			writer.write("otp_ecc_writer.dat");
			
			begin
				logic[11:0] data[$] = {};
				read_otp("otp_ecc_writer.dat", 8, data);
				
				`FAIL_UNLESS_EQUAL(data[0], 12'h190);
				`FAIL_UNLESS_EQUAL(data[1], 12'h200);
				`FAIL_UNLESS_EQUAL(data[2], 12'hdaf);
				`FAIL_UNLESS_EQUAL(data[3], 12'h2fe);
				`FAIL_UNLESS_EQUAL(data[4], 12'hc90);
				`FAIL_UNLESS_EQUAL(data[5], 12'hf01);
				`FAIL_UNLESS_EQUAL(data[6], 12'h3d0);
				`FAIL_UNLESS_EQUAL(data[7], 12'h80f);
			end
		`SVTEST_END
			
		`SVTEST ("address_data_otp_entry_test")
			address_data_otp_entry e = new();
			`FAIL_IF_EQUAL(e.randomize() with {
					address == 12'h800; 
					data == 16'haffe; 
					single_bit_address_ecc_failure == 1'b0;
					double_bit_address_ecc_failure == 1'b0;
					single_bit_data_ecc_failure == 1'b0;
					double_bit_data_ecc_failure == 1'b0;
					}, 0);
						
			`FAIL_UNLESS_EQUAL(4, e.get_value_count());
			`FAIL_UNLESS_EQUAL(12'h208, e.get_value(0, 0));
			`FAIL_UNLESS_EQUAL(12'h500, e.get_value(1, 1));
			`FAIL_UNLESS_EQUAL(12'hdaf, e.get_value(2, 2));
			`FAIL_UNLESS_EQUAL(12'h2fe, e.get_value(3, 3));
		`SVTEST_END
			
		`SVTEST ("address_data_otp_entry_single_failure_test")
			address_data_otp_entry e = new();
			`FAIL_IF_EQUAL(e.randomize() with {
					address == 12'h0800; 
					data == 16'haffe; 
					single_bit_address_ecc_failure 	== 1'b1;
					first_address_failure_position 	== 0;
					double_bit_address_ecc_failure	== 1'b0;
					single_bit_data_ecc_failure	 	== 1'b0;
					double_bit_data_ecc_failure		== 1'b1;
					first_data_failure_position 	== 0;
					second_data_failure_position	== 23;
				}, 0);
						
			`FAIL_UNLESS_EQUAL(4, e.get_value_count());
			`FAIL_UNLESS_EQUAL(12'h208, e.get_value(0, 0));
			`FAIL_UNLESS_EQUAL(12'h501, e.get_value(1, 1));
			`FAIL_UNLESS_EQUAL(12'h5af, e.get_value(2, 2));
			`FAIL_UNLESS_EQUAL(12'h2ff, e.get_value(3, 3));
		`SVTEST_END
			
	`SVUNIT_TESTS_END

endmodule
