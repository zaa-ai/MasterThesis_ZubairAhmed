`include "svunit_defines.svh"

module dsi3_filter_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import dsi3_slave_pkg::*;
	import uvm_pkg::*;
	import unit_test_pkg::*;
	import common_env_pkg::*;
	import dsi3_pkg::*;

	string name = "dsi3_filter_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	
	`clk_def(27777ps)
	
	`tick_gen
	
	dsi3_chip_if chip_filtered_if ();
	
	typedef	enum logic[1:0] {C0=2'd0, C1=2'd1, C2=2'd3} chips_e;
	chips_e	rx, chip_filtered;
	dsi3_pkg::dsi3_chip	expected_chip;
	// @SuppressProblem -type fully_unread_static_variable -count 1 -length 1
	
	logic[1:0]	rx_as_chip_logic;
	dsi3_pkg::dsi3_chip	rx_as_chip;
	bit	miscompare;
	logic	short_filter_time;
	
	dsi3_filter dsi3_filter (
		.clk_rst               (clk_rst.slave     ), 
		.i_rx                  (rx                ),
		.i_shorter_filter_time (short_filter_time ),
		.chip_filtered         (chip_filtered_if.master ), 
		.o_rx_test             (                  ));
	
	/*###   for debug viewing only!   ######################################################*/
	chip_conversion_rx_to_chip i_chip_conversion_rx_to_chip (
		.in   (rx  ), 
		.out  (rx_as_chip_logic ));
	assign rx_as_chip = dsi3_pkg::dsi3_chip'(rx_as_chip_logic);
	/*################################################################################*/
	
	always_comb begin
		chip_filtered = convert_to_chips_e(chip_filtered_if.chip);
	end
	
	initial begin
		forever begin
			@(chip_filtered_if.chip or expected_chip);
			if (expected_chip !== 2'bxx) begin
				if (chip_filtered_if.chip != expected_chip) begin
					miscompare |= 1'b1;
				end
			end
		end
	end
	
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
		rx = chips_e'(0);
		expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
		miscompare = 1'b0;
		short_filter_time = 1'b0;
		#1us;
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
		#1us;
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
	begin
		chips_e	from, to;
		time t_start, t_end;

		enable_clk = 1'b1;
		#10us;
		
		from = C0;
		to = C0;
		for (int filter_time = 1; filter_time >= 0; filter_time--) begin
			do begin
				do begin
					`SVTEST($sformatf("Check filter %s -> %s with short_filter_time=%1b", from.name(), to.name() , (filter_time > 0) ? 1'b1 : 1'b0))
						short_filter_time = (filter_time > 0) ? 1'b1 : 1'b0;
						set_initial_chip(from);
						t_start = $time();
						rx = to;
						fork
							#2us;
							begin
								@chip_filtered;
								t_end = $time();
								#0.5us;
							end
							begin
								expected_chip = convert_to_dsi3_chip(from);
								if (short_filter_time == 1'b1) #570ns; else #850ns;
								expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
								#205ns;
								expected_chip = convert_to_dsi3_chip(to);
							end
						join_any
						disable fork;
						`FAIL_UNLESS_EQUAL(chip_filtered, to)
						if (from != to) begin
							`FAIL_UNLESS_SMALLER((t_end - t_start), 1us)
						end
						`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
					`SVTEST_END
					to = to.next();
				end while (to != from.first);
				from = from.next();
			end while (from != from.first);
		end
		
		`SVTEST($sformatf("Check filter for simulation p52143_399"))
			bit fail = 1'b0;
			set_initial_chip(C0);
			
			fork
				begin
					rx = C1;
					#0.736us;
					rx = C2;
					#0.72us;
					rx = C1;
					#1.598us;
					rx = C0;
					#1.122us;
					rx = C1;
					#0.72us;
					rx = C0;
					#2us;
				end
				begin // expectation
					expected_chip = dsi3_pkg::C0;
					#850ns;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C1;
					#2.85us;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C0;
				end
			join
			
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
		
		`SVTEST($sformatf("Check filter with stair C0 -> C2"))
			set_initial_chip(C0);
			
			fork
				begin
					rx = C1;
					#500ns;
					rx = C2;
					#2us;
				end
				begin
					#1us;
					`FAIL_UNLESS_EQUAL(chip_filtered, C1)
					#500ns;
					`FAIL_UNLESS_EQUAL(chip_filtered, C2)
				end
				begin
					expected_chip = dsi3_pkg::C0;
					#850ns;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C1;
					#300ns;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C2;
				end
			join
			`FAIL_UNLESS_EQUAL(chip_filtered, C2)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
		
		`SVTEST($sformatf("Check filter with stair C2 -> C0"))
			set_initial_chip(C2);
			
			fork
				begin
					rx = C1;
					#500ns;
					rx = C0;
					#1us;
				end
				begin
					#1us;
					`FAIL_UNLESS_EQUAL(chip_filtered, C1)
					#500ns;
					`FAIL_UNLESS_EQUAL(chip_filtered, C0)
				end
				begin
					expected_chip = dsi3_pkg::C2;
					#850ns;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C1;
					#300ns;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C0;
				end
			join
			`FAIL_UNLESS_EQUAL(chip_filtered, C0)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
			
		`SVTEST($sformatf("Check filter noise C0 -> C1 -> C2 -> C1 -> C2 ..."))
			set_initial_chip(C0);
			
			fork
				begin
					rx = C1;
					#500ns;
					repeat(5) begin
						rx = C2;
						#500ns;
						rx = C1;
						#500ns;
					end
				end
				begin
					expected_chip = dsi3_pkg::C0;
					#850ns;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C1;
				end
			join
			`FAIL_UNLESS_EQUAL(chip_filtered, C1)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
			
		`SVTEST($sformatf("Check filter noise C0 -> C2 -> C1 -> C2 ..."))
			set_initial_chip(C0);
			
			fork
				begin
					rx = C2;
					#500ns;
					repeat(5) begin
						rx = C1;
						#500ns;
						rx = C2;
						#500ns;
					end
				end
				begin
					expected_chip = dsi3_pkg::C0;
					#850ns;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#200ns;
					expected_chip = dsi3_pkg::C1;
				end
			join
			`FAIL_UNLESS_EQUAL(chip_filtered, C1)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
			
				
		`SVTEST($sformatf("Check filter noise C0 -> C2 -> C0 -> C2 ..."))
			set_initial_chip(C0);
			expected_chip = dsi3_pkg::C0;
			rx = C2;
			#500ns;
			repeat(5) begin
				rx = C0;
				#500ns;
				rx = C2;
				#500ns;
			end
			`FAIL_UNLESS_EQUAL(chip_filtered, C0)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
				
		`SVTEST($sformatf("Check filter noise C1 -> C2 -> C1 -> C2 ..."))
			set_initial_chip(C1);
			expected_chip = dsi3_pkg::C1;
			
			rx = C1;
			#500ns;
			repeat(5) begin
				rx = C1;
				#500ns;
				rx = C2;
				#500ns;
			end
			`FAIL_UNLESS_EQUAL(chip_filtered, C1)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
				
		`SVTEST($sformatf("Check filter noise C1 -> C0 -> C1 -> C0 ..."))
			set_initial_chip(C1);
			expected_chip = dsi3_pkg::C1;
			
			rx = C1;
			#500ns;
			repeat(5) begin
				rx = C1;
				#500ns;
				rx = C0;
				#500ns;
			end
			`FAIL_UNLESS_EQUAL(chip_filtered, C1)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
			
		`SVTEST($sformatf("Check filter noise C1 -> C0 -> C2 -> C0 ..."))
			set_initial_chip(C1);
			expected_chip = dsi3_pkg::C1;
			
			rx = C1;
			#500ns;
			repeat(5) begin
				rx = C0;
				#500ns;
				rx = C2;
				#500ns;
			end
			`FAIL_UNLESS_EQUAL(chip_filtered, C1)
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
		`SVTEST_END
		
		for (time period=0.1us; period<0.71us; period+=0.1us) begin
			chips_e	mid_value = mid_value.first;
			do begin
				`SVTEST($sformatf("Check filter noise sine at %s with period %7.3fus", mid_value.name, period/1.0us))
					set_initial_chip(mid_value);
					expected_chip = convert_to_dsi3_chip(mid_value);

					repeat(10) begin
						make_sine(period, mid_value);
					end
					`FAIL_UNLESS_EQUAL(chip_filtered, mid_value)
					`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
				`SVTEST_END
				mid_value = mid_value.next();
			end while (mid_value != mid_value.first);
		end
		
		`SVTEST($sformatf("Check filter triangle"))
			real chip = 2.5;
			set_initial_chip(C2);
			#500ns;
			
			fork
				repeat(30) begin
					repeat(10) begin
						chip-=0.1;
						rx = real_to_chip(chip);
						#25ns;
					end
					repeat(9) begin
						chip+=0.1;
						rx = real_to_chip(chip);
						#25ns;
					end
				end
				begin
					expected_chip = dsi3_pkg::C2;
					#3.9us;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#600ns;
					expected_chip = dsi3_pkg::C1;
					#4.3us;
					expected_chip = dsi3_pkg::dsi3_chip'(2'bxx);
					#600ns;
					expected_chip = dsi3_pkg::C0;
					#500ns;
				end
			join
			`FAIL_UNLESS_EQUAL(miscompare, 1'b0)
			`FAIL_UNLESS_EQUAL(chip_filtered, C0)
		`SVTEST_END
		
		from = C0;
		to = C0;
		do begin
			do begin
				if (from != to) begin
					for (int dc=1; dc<10; dc++) begin
						`SVTEST($sformatf("Check filter RX toggling between %s and %s with DC=0.%02d", from.name(), to.name(), dc))
							set_initial_chip(from);
							repeat(50) begin
								rx = to;
								#(dc*100ns);
								rx = from;
								#((10-dc)*100ns);
							end
							if (dc > 5) begin
								`FAIL_UNLESS_EQUAL(chip_filtered, to)
							end
							else begin
								`FAIL_UNLESS_EQUAL(chip_filtered, from)
							end
						`SVTEST_END
					end
				end
				to = to.next();
			end while (to != from.first);
			from = from.next();
		end while (from != from.first);
			
			// 1-2-1-2
			// 1-2-0-2-0-2..
			
		enable_clk = 1'b0;
	end	 
	`SVUNIT_TESTS_END
	
	task automatic make_sine(input time period, input chips_e mid_value);
		real pi_over_6 = 0.52359877559829887307710723054658;
		rx = mid_value;
		#((pi_over_6 / 2.0) * period);
		rx = increment_chip(mid_value);
		#((4.0 * pi_over_6 / 2.0) * period);
		rx = mid_value;
		#((2.0 * pi_over_6 / 2.0) * period);
		rx = decrement_chip(mid_value);
		#((4.0 * pi_over_6 / 2.0) * period);
		rx = mid_value;
		#((pi_over_6 / 2.0) * period);
	endtask
	
	function automatic chips_e convert_to_chips_e(dsi3_pkg::dsi3_chip in);
		case (in)
			dsi3_pkg::C0: return C0;
			dsi3_pkg::C1: return C1;
			dsi3_pkg::C2: return C2;
		endcase
		return chips_e'(2'bxx);
	endfunction
	
	function automatic dsi3_pkg::dsi3_chip convert_to_dsi3_chip(chips_e	in);
		case(in)
			C0: return dsi3_pkg::C0;
			C1: return dsi3_pkg::C1;
			C2: return dsi3_pkg::C2;
		endcase
		return CX;
	endfunction
		
	task automatic set_initial_chip(input chips_e initial_chip);
		rx = initial_chip;
		#2us;
		`FAIL_UNLESS_EQUAL(chip_filtered, initial_chip)
	endtask
	
	function automatic chips_e real_to_chip(real	value);
		if (value >= 1.5)
			return C2;
		else begin
			if (value >= 0.5) 
				return C1;
			else
				return C0;
		end
	endfunction
		
	function automatic chips_e increment_chip(chips_e in);
		case (in)
			C0: return C1;
			C1: return C2;
			default: return C2;
		endcase
	endfunction
	
	function automatic chips_e decrement_chip(chips_e in);
		case (in)
			C1: return C0;
			C2: return C1;
			default: return C0;
		endcase
	endfunction
	
endmodule
