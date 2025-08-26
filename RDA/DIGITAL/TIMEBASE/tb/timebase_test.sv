`include "svunit_defines.svh"

class clk_error_results;
	real	min;
	real	max;
	real	results[$];
	
	function new(real lower_initial_value = 0.0, real upper_initial_value = 1.0);
		min = upper_initial_value;
		max = lower_initial_value;
	endfunction
	
	function void add_result(real value);
		results.push_back(value);
		if (value < min)	min = value;
		if (value > max)	max = value;
	endfunction
	
	function void display_results(string prefix);
		$display("%s min=%7.3f, max=%7.3f",prefix, min, max);
	endfunction
	
endclass

module timebase_test import project_pkg::*; ();
	import svunit_pkg::svunit_testcase;
	import addresses_pkg::*;
	import common_test_pkg::*;

	string name = "timebase_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	
	clk_error_results	err_ul, err_ll;
	
	elip_if #(.addr_width(ELIP_ADDR_WIDTH), .data_width(DATA_WIDTH)) elip_vif(); 
	l16				o_elip_out; 
	task elip_read(input elip_addr_t addr, output elip_data_t elip_data_out); 
		@(negedge clk_switched_rst.clk); 
		elip_vif.rd = 1'b1; 
		elip_vif.addr = addr;
		#10ns;
		elip_data_out = o_elip_out;
		@(posedge clk_switched_rst.clk);
		#1ns;
		
		#5ns;
		elip_idle(); 
	endtask 
	task elip_write(input elip_addr_t addr, elip_data_t data); 
		@(negedge clk_switched_rst.clk); 
		elip_vif.wr = 1'b1; 
		elip_vif.addr = addr; 
		elip_vif.data_write = data; 
		@(posedge clk_switched_rst.clk);
		#5ns;
		elip_idle();
	endtask 
	task elip_idle(); 
		elip_vif.rd = 1'b0; 
		elip_vif.wr = 1'b0;
		elip_vif.addr = '0;
		elip_vif.data_write = '0;
	endtask

	initial begin
		elip_idle();
	end

	task check_elip(elip_addr_t addr, elip_data_t data);
		l16 elip_data_out;
		elip_read(addr, elip_data_out);
		`FAIL_UNLESS_EQUAL (elip_data_out, data)
	endtask

	
	clk_reset_if	clk_switched_rst (); 
	clk_reset_if	clkosc_rst (); 
	clock_switch_if clock_switch_io ();
	
	assign clkosc_rst.rstn = clk_switched_rst.rstn;
	
	tmr_osc_if tmr_osc ();
	tmr_out_osc_if tmr_out_osc ();
	jtag_bus_if #(.addr_width (JTAG_IR_WIDTH ), .data_width  (JTAG_DR_WIDTH )) jtag_bus ();
	
	`clk_def(27777ps)

	initial begin
		err_ul = new(1.0, 2.0);
		err_ll = new();
		set_por();
	end
		
	assign	clk_switched_rst.rstn = clk_rst.rstn;
	logic	use_oscillator_model_clock = 1'b1;
	logic clkref_enable, clkref; 
	time clock_period_half_clkref = 1us;
	
	logic	clk_osc;
	assign	clkosc_rst.clk = (use_oscillator_model_clock == 1'b1) ? clk_osc : clk_rst.clk;
	
	initial begin 
		clkref = 1'b0; 
		clkref_enable = 1'b0; 
		forever begin 
			if (clkref_enable) begin 
				clkref = 1'b0; 
				#(clock_period_half_clkref); 
				clkref = 1'b1; 
				#(clock_period_half_clkref); 
			end 
			else begin 
				@(posedge clkref_enable); 
			end 
		end 
	end 
	
	timebase_info_if timebase_info();
	timebase_io_if timebase_io ();
	
	pll_top i_pll_top (
		.ATST_PLL      ('0     ), 
		.CLKREF        (timebase_io.clkref_div       ), 
		.RESB          (clk_switched_rst.rstn ), 
		.ON_PLL        (timebase_io.pll_on       ), 
		.PLL_HOLD      (timebase_io.pll_hold     ), 
		.PLL_LOCK_MON  ( ), 
		.PLL_UP_MON    (   ), 
		.CLKPLL        (timebase_io.clkpll       ), 
		.CLKPLL_DIV    (timebase_io.clkpll_div   ), 
		.PLL_DOWN_MON  ( ), 
		.VDD           (1.8          ), 
		.GND           (0.0          )
	);
	
	logic	osc_ready;
	
	osc_trim #(
		.trim_size(7),
		.tfmin(41.6ns),
		.tstep(0.184ns)
	) xosc_trim (
		.vss(0.0),
		.vsub(0.0),
		.vdd(1.8),
		.trim(timebase_io.trim_osc_f),
		.trim_tcf (timebase_io.trim_osc_tcf),
		.osc_ready      (osc_ready     ), 
		.TST_OSC_SFMAX(1'b0),
		.TST_OSC_SFMIN(1'b0),
		.enable(1'b1),
		.clk_out(clk_osc)
		//			,.ATST_OSC	   (ATST_OSC     )
		//			,.AOUT(AOUT)
	);
	
	//*###   Clock Switch OSC/PLL   ######################################################*/
	logic tst_clksw_en, tst_clksw_sel;
	initial tst_clksw_en = 1'b0;
	initial tst_clksw_sel = 1'b0;
	clock_switch i_clock_switch (
			.i_clk1     	(clkosc_rst.clk    ), 
			.i_clk2     	(timebase_io.clkpll    ), 
			.i_sel_clk2  	(clock_switch_io.select_clock_pll),
			.i_rstn     	(clk_switched_rst.rstn), 
			.i_tst_en		(tst_clksw_en),
			.i_tst_sel		(tst_clksw_sel),
			.o_clk			(clk_switched_rst.clk   ),
			.o_clk_switched	(clock_switch_io.clock_switched)
		);
	
	logic	pll_monitor_locked, clkref_ok_monitor_signal;
	logic	[DSI_CHANNELS-1:0]	transmit_pending;
	
	initial begin
		transmit_pending = '0;
	end
	
	assign timebase_io.clkref = clkref;
	
	initial begin
		jtag_bus.rstn = 1'b1;
		#1ns jtag_bus.rstn = 1'b0;
	end
	
	timebase #(
		.base_addr           (BASE_ADDR_TIMEBASE ), 
		.addr_width          (ELIP_ADDR_WIDTH    ), 
		.DSI3_COUNT          (4			         )
	) i_timebase (
		.clk_rst             (clk_switched_rst.slave   ), 
		.clkosc_rst          (clkosc_rst.slave         ),
		.timebase_info       (timebase_info.master      ),
		.timebase_io         (timebase_io.master        ),
		.tmr_osc             (tmr_osc.master            ),
		.tmr_out_osc         (tmr_out_osc.master        ),
		.jtag_bus            (jtag_bus.slave           ), 
		.o_jtag_dr           (                   ), 
		.elip                (elip_vif.slave           ), 
		.i_transmit_pending  (transmit_pending   ), 
		.o_elip_data_read    (o_elip_out         ), 
		.clock_switch_io     (clock_switch_io.timebase    ),
		.i_scanmode          (1'b0               )
	);
	
	assign	clkref_ok_monitor_signal = i_timebase.clkref_ok;
	assign	pll_monitor_locked = i_timebase.pll_locked;
	assign	tmr_out_osc.clock_selected = 1'b0;
	
	typedef enum logic[6:0] {NORMAL='h4b, LOW='h46, HIGH='h50} clk_trimming;
	typedef enum logic[1:0] {NO_CLKREF, CLKREF_VALID, PLL_LOCKED, PLL_HOLD} timebase_state;
	clk_trimming	trim = NORMAL;
	typedef enum {NORMAL_F=27777, LOW_F=28636, HIGH_F=26969} clk_frequency_e;
	clk_frequency_e	clk_freq = NORMAL_F;
	
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
		elip_idle();
		#10ns;
		elip_write(ADDR_TIMEBASE_TRIM_OSC, trim);
		elip_write(ADDR_TIMEBASE_TRIM_OSC_TCF, 16'd0);
		clkref_enable = 1'b0;
		clock_period_half = clk_freq * 1ps;
		#20us;
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
		#1us;
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
	localparam NOTEST = 1;
	localparam time lower_limit[3:0] = '{3840000, 1920000, 960000, 480000};
	localparam time upper_limit[3:0] = '{4160000, 2080000, 1040000, 520000};
	
	
	//           CLKREF_CONF | OSC_TRIM | UP/DOWN
	real	clkref_err_ll  [3:0][1:0][1:0];
	real	clkref_err_ul  [3:0][1:0][1:0];
	time	clkref_err_ll_f[3:0][1:0][1:0];
	time	clkref_err_ul_f[3:0][1:0][1:0];
	
	real	current_clkref_nominal_frequency;
	
	function void set_clk(clk_frequency_e freq);
		clk_freq = freq;
		clock_period_half = clk_freq * 1ps;
	endfunction
	
	//TODO: add test for clkref_ok
	`SVUNIT_TESTS_BEGIN
		#1us;
		enable_clk = 1'b1;
		
		`SVTEST("Check frequency trimming")
			int trimming = $urandom();
			elip_write(ADDR_TIMEBASE_TRIM_OSC, trimming);
			
			`FAIL_UNLESS_EQUAL(trimming[TRIM_OSC_F_WIDTH-1:0], timebase_io.trim_osc_f)
			check_elip(ADDR_TIMEBASE_TRIM_OSC, trimming[TRIM_OSC_F_WIDTH-1:0]);
		`SVTEST_END
			
		`SVTEST("Check frequency steps")
			realtime start, diff;
			for (logic[6:0] trim=7'h40; trim < 7'h68; trim+=7'd1) begin
				elip_write(ADDR_TIMEBASE_TRIM_OSC, trim);
				#1us;
				@(posedge clkosc_rst.clk);
				start = $realtime();
				@(posedge clkosc_rst.clk);
				diff = $realtime() - start;
				$display("Frequency = %5.2f @ trim=%2h", 1.0us/diff, trim);
			end
		`SVTEST_END
			
		`SVTEST("Check frequency temp coefficient trimming")
			int trimming = $urandom();
			elip_write(ADDR_TIMEBASE_TRIM_OSC_TCF, trimming);
			
			`FAIL_UNLESS_EQUAL(trimming[TRIM_OSC_TCF_WIDTH-1:0], timebase_io.trim_osc_tcf)
			check_elip(ADDR_TIMEBASE_TRIM_OSC_TCF, trimming[TRIM_OSC_TCF_WIDTH-1:0]);
		`SVTEST_END
			
		`SVTEST("Check 1us tick")
			fork
				begin
					@(posedge timebase_info.tick_1us);
				end
				begin
					bit timeout_1us = 1'b1;
					#2us;
					`FAIL_IF(timeout_1us)
				end
			join_any
			disable fork;
			repeat (18)
				@(posedge clk_switched_rst.clk);
			#10ns;
			`FAIL_UNLESS_EQUAL(timebase_info.tick_1us, 1'b1)
		`SVTEST_END
		
		`SVTEST("Check 1ms tick")
			fork
				begin
					do begin
						@(posedge timebase_info.tick_1ms);
					end
					while (timebase_info.tick_1ms != 1'b1);
				end
				begin
					bit timeout_1ms = 1'b1;
					#1.5ms;
					`FAIL_IF(timeout_1ms)
				end
			join_any
			disable fork;
			repeat (18*1024)
				@(posedge clk_switched_rst.clk);
			#10ns;
			`FAIL_UNLESS_EQUAL(timebase_info.tick_1ms, 1'b1)
		`SVTEST_END
			
		`SVTEST("Check time base")
			int tb1, tb2;
			elip_read(ADDR_TIMEBASE_TB_CNT, tb1);
			#10us;
			elip_read(ADDR_TIMEBASE_TB_CNT, tb2);
			`FAIL_UNLESS_EQUAL(tb1+'d10, tb2)
		`SVTEST_END
		
		
		use_oscillator_model_clock = 1'b0;
		
		set_clk(LOW_F);
		
		for (int clkref_divivder_setting = 0; clkref_divivder_setting < 4; clkref_divivder_setting++) begin
			int lowest_limit = 400000 * (1<<clkref_divivder_setting);
			int uppest_limit = 600000 * (1<<clkref_divivder_setting);
			int	freq_corner=0;
			current_clkref_nominal_frequency = 500000.0 * (1 << clkref_divivder_setting);
			
			do begin
				clkref_enable = 1'b0;
				#10us;
				elip_write(ADDR_TIMEBASE_CLKREF_CONF, clkref_divivder_setting);
				#10us;
				clock_period_half_clkref = 1.0us / (1<<clkref_divivder_setting);
				#10us;
				clkref_enable = 1'b1;
				#10us;
				
				`SVTEST($sformatf("CLKREF mon low limit from NOK | clk_freq=%s | CLKREF div=%2b", clk_freq, clkref_divivder_setting))
					automatic time clkref_lower_limit_half_period = time'(0);
					clock_period_half_clkref = 1.4us / (1<<clkref_divivder_setting);
					clkref_enable = 1'b1;
					#500us;
					`FAIL_IF_EQUAL(clkref_ok_monitor_signal, 1'b1)
					fork
						begin
							for (clock_period_half_clkref = clock_period_half_clkref; clock_period_half_clkref > (1us / (1<<clkref_divivder_setting)); clock_period_half_clkref-=0.001us) begin
								#10us;
							end
						end
						begin
							@(posedge clkref_ok_monitor_signal);
							clkref_lower_limit_half_period = clock_period_half_clkref;
							@(negedge clkref_ok_monitor_signal);
							begin
								bit clkref_ok_went_low_after_detecting_clkref_ok = 1'b1;
								`FAIL_IF(clkref_ok_went_low_after_detecting_clkref_ok)
							end
						end
					join_any
					disable fork;
					begin
						time clkref_lower_limit = get_frequency(clkref_lower_limit_half_period);
						$display("CLKREF lower limit = %0dHz", clkref_lower_limit);
						$display("CLKREF lower limit = %7.3f", clkref_lower_limit/current_clkref_nominal_frequency);
						err_ll.add_result(clkref_lower_limit/current_clkref_nominal_frequency);
						clkref_err_ll[clkref_divivder_setting][freq_corner][0] = clkref_lower_limit/current_clkref_nominal_frequency;
						clkref_err_ll_f[clkref_divivder_setting][freq_corner][0] = clkref_lower_limit;
						`FAIL_UNLESS_SMALLER(clkref_lower_limit, lower_limit[clkref_divivder_setting], d)
						`FAIL_UNLESS_GREATER(clkref_lower_limit, lowest_limit, d)
					end
				`SVTEST_END
				
				`SVTEST($sformatf("CLKREF mon low limit from OK | clk_freq=%s | CLKREF div=%2b", clk_freq, clkref_divivder_setting))
					automatic time clkref_lower_limit_half_period = 0s;
					clock_period_half_clkref = 1.0us / (1<<clkref_divivder_setting);
					clkref_enable = 1'b1;
					#500us;
					`FAIL_IF_EQUAL(clkref_ok_monitor_signal, 1'b0)
					fork
						begin
							for (clock_period_half_clkref = clock_period_half_clkref; clock_period_half_clkref < (1.2us / (1<<clkref_divivder_setting)); clock_period_half_clkref+=0.001us) begin
								#10us;
							end
						end
						begin
							@(negedge clkref_ok_monitor_signal);
							clkref_lower_limit_half_period = clock_period_half_clkref;
							@(posedge clkref_ok_monitor_signal);
							begin
								bit clkref_ok_went_high_after_detecting_clkref_nok = 1'b1;
								`FAIL_IF(clkref_ok_went_high_after_detecting_clkref_nok)
							end
						end
					join_any
					disable fork;
					begin
						time clkref_lower_limit = get_frequency(clkref_lower_limit_half_period);
						$display("CLKREF lower limit = %0dHz", clkref_lower_limit);
						$display("CLKREF lower limit = %7.3f", clkref_lower_limit/current_clkref_nominal_frequency);
						err_ll.add_result(clkref_lower_limit/current_clkref_nominal_frequency);
						clkref_err_ll[clkref_divivder_setting][freq_corner][1] = clkref_lower_limit/current_clkref_nominal_frequency;
						clkref_err_ll_f[clkref_divivder_setting][freq_corner][1] = clkref_lower_limit;
						`FAIL_UNLESS_SMALLER(clkref_lower_limit, lower_limit[clkref_divivder_setting], d)
						`FAIL_UNLESS_GREATER(clkref_lower_limit, lowest_limit, d)
					end
				`SVTEST_END
				
				`SVTEST($sformatf("CLKREF mon high limit from OK | clk_freq=%s | CLKREF div=%2b", clk_freq, clkref_divivder_setting))
					automatic time clkref_upper_limit_half_period = 0s;
					clock_period_half_clkref = 1.0us / (1<<clkref_divivder_setting);
					clkref_enable = 1'b1;
					#500us;
					`FAIL_IF_EQUAL(clkref_ok_monitor_signal, 1'b0)
					fork
						begin
							for (clock_period_half_clkref = clock_period_half_clkref; clock_period_half_clkref > (0.8us / (1<<clkref_divivder_setting)); clock_period_half_clkref-=0.001us) begin
								#10us;
							end
						end
						begin
							@(negedge clkref_ok_monitor_signal);
							clkref_upper_limit_half_period = clock_period_half_clkref;
							@(posedge clkref_ok_monitor_signal);
							begin
								bit clkref_ok_went_high_after_detecting_clkref_nok = 1'b1;
								`FAIL_IF(clkref_ok_went_high_after_detecting_clkref_nok)
							end
						end
					join_any
					disable fork;
					begin
						time clkref_upper_limit = get_frequency(clkref_upper_limit_half_period);
						$display("CLKREF upper limit = %0dHz", clkref_upper_limit);
						$display("CLKREF upper limit = %7.3f", clkref_upper_limit/current_clkref_nominal_frequency);
						err_ul.add_result(clkref_upper_limit/current_clkref_nominal_frequency);
						clkref_err_ul[clkref_divivder_setting][freq_corner][0] = clkref_upper_limit/current_clkref_nominal_frequency;
						clkref_err_ul_f[clkref_divivder_setting][freq_corner][0] = clkref_upper_limit;
						`FAIL_UNLESS_SMALLER(clkref_upper_limit, uppest_limit, d)
						`FAIL_UNLESS_GREATER(clkref_upper_limit, upper_limit[clkref_divivder_setting], d)
					end
				`SVTEST_END
					
				`SVTEST($sformatf("CLKREF mon high limit from NOK | clk_freq=%s | CLKREF div=%2b", clk_freq, clkref_divivder_setting))
					automatic time clkref_upper_limit_half_period = 0s;
					clock_period_half_clkref = 0.6us / (1<<clkref_divivder_setting);
					clkref_enable = 1'b1;
					#500us;
					`FAIL_IF_EQUAL(clkref_ok_monitor_signal, 1'b1)
					fork
						begin
							for (clock_period_half_clkref = clock_period_half_clkref; clock_period_half_clkref < (1us / (1<<clkref_divivder_setting)); clock_period_half_clkref+=0.001us) begin
								#10us;
							end
						end
						begin
							@(posedge clkref_ok_monitor_signal);
							clkref_upper_limit_half_period = clock_period_half_clkref;
							@(negedge clkref_ok_monitor_signal);
							begin
								bit clkref_ok_went_low_after_detecting_clkref_ok = 1'b1;
								`FAIL_IF(clkref_ok_went_low_after_detecting_clkref_ok)
							end
						end
					join_any
					disable fork;
					begin
						time clkref_upper_limit = get_frequency(clkref_upper_limit_half_period);
						$display("CLKREF upper limit = %0dHz", clkref_upper_limit);
						$display("CLKREF upper limit = %7.3f", clkref_upper_limit/current_clkref_nominal_frequency);
						err_ul.add_result(clkref_upper_limit/current_clkref_nominal_frequency);
						clkref_err_ul[clkref_divivder_setting][freq_corner][1] = clkref_upper_limit/current_clkref_nominal_frequency;
						clkref_err_ul_f[clkref_divivder_setting][freq_corner][1] = clkref_upper_limit;
						`FAIL_UNLESS_SMALLER(clkref_upper_limit, uppest_limit, d)
						`FAIL_UNLESS_GREATER(clkref_upper_limit, upper_limit[clkref_divivder_setting], d)
					end
				`SVTEST_END
				set_clk(clk_freq.next);
				freq_corner++;
			end while (clk_freq != clk_freq.first());
			elip_write(ADDR_TIMEBASE_CLKREF_CONF, 0);
			clock_period_half_clkref = 1us;
		end
		
		`SVTEST("List results")
			err_ll.display_results("err_ll=");
			err_ul.display_results("err_ul=");
		`SVTEST_END
		
		`SVTEST("List results")
			$write("\t\t\t");
			repeat(2)
				$write("OK->NOK\t\tNOK->OK\t\t");
			$display("");
			for (int clkref_divivder_setting=0; clkref_divivder_setting < 4; clkref_divivder_setting++) begin
				for (int freq_corner=0; freq_corner<2; freq_corner++) begin
					$write("CLKREF_CONF=%1d, CLK=%s\t", clkref_divivder_setting, (freq_corner)?"HIGH":"LOW");
					for (int up=0; up < 2; up++) begin
						$write("%7.3f\t\t", clkref_err_ll[clkref_divivder_setting][freq_corner][up]);
					end
					for (int up=0; up < 2; up++) begin
						$write("%7.3f\t\t", clkref_err_ul[clkref_divivder_setting][freq_corner][up]);
					end
					$display("");
				end
            end
            for (int clkref_divivder_setting=0; clkref_divivder_setting < 4; clkref_divivder_setting++) begin
                for (int freq_corner=0; freq_corner<2; freq_corner++) begin
                    for (int up=0; up < 2; up++) begin
                        $display("[sim:measure] 'f__CLKREF,err,ll__/f__CLKREF__' = '%5.2f'", clkref_err_ll[clkref_divivder_setting][freq_corner][up]);
                    end
                    for (int up=0; up < 2; up++) begin
                        $display("[sim:measure] 'f__CLKREF,err,ul__/f__CLKREF__' = '%5.2f'", clkref_err_ul[clkref_divivder_setting][freq_corner][up]);
                    end
                end
            end
            $display("[sim:measure] 'CLKREF Supervision' status=PASS");
		`SVTEST_END
			
		`SVTEST("List results [f]")
			$write("\t\t\t");
			repeat(2)
				$write("OK->NOK\t\tNOK->OK\t\t");
			$display("");
			for (int clkref_divivder_setting=0; clkref_divivder_setting < 4; clkref_divivder_setting++) begin
				for (int freq_corner=0; freq_corner<2; freq_corner++) begin
					$write("CLKREF_CONF=%1d, CLK=%s\t", clkref_divivder_setting, (freq_corner)?"HIGH":"LOW");
					for (int up=0; up < 2; up++) begin
						$write("%7.3f\t\t", clkref_err_ll_f[clkref_divivder_setting][freq_corner][up]);
					end
					for (int up=0; up < 2; up++) begin
						$write("%7.3f\t\t", clkref_err_ul_f[clkref_divivder_setting][freq_corner][up]);
					end
					$display("");
				end
			end
		`SVTEST_END
		
		trim = NORMAL;
		clock_period_half_clkref = 1us;
		set_clk(NORMAL_F);
		
		`SVTEST("Check PLL_ON")
			clkref_enable = 1'b1;
			fork
				begin
					@(posedge clkref_ok_monitor_signal);
				end
				begin
					#10us;
					`FAIL_UNLESS_EQUAL(clkref_ok_monitor_signal, 1'b1)
				end
			join_any
			disable fork;
			#1us;
			check_timebase_state(CLKREF_VALID);
		`SVTEST_END
		
		`SVTEST("Check PLL monitor")
			clkref_enable = 1'b1;
			#10us;
			check_timebase_state(CLKREF_VALID);
			#290us;
			check_timebase_state(PLL_LOCKED);
		`SVTEST_END
		
		for (int channel=1; channel<4; channel++) begin
			`SVTEST($sformatf("PLL hold if transmission on channel %2b is pending and CLKREF is erroneous", channel[1:0]))
				clkref_enable = 1'b1;
				#300us;
				check_timebase_state(PLL_LOCKED);
				transmit_pending = $size(transmit_pending)'(channel);
				#1us;
				clkref_enable = 1'b0;
				#4us;
				check_timebase_state(PLL_HOLD, 0, 1);
				#500us;
				check_timebase_state(PLL_HOLD, 0, 1);
				transmit_pending = 4'b00;
				#0.5us;
				check_timebase_state(NO_CLKREF);
			`SVTEST_END
		end
		
		for (int channel=1; channel<3; channel++) begin
			`SVTEST($sformatf("PLL hold if transmission on channel %1d is pending and CLKREF is erroneous and other channel %1d gets pending afterwards", channel, ~(channel[1:0])))
				clkref_enable = 1'b1;
				#300us;
				check_timebase_state(PLL_LOCKED);
                transmit_pending = $size(transmit_pending)'(channel);
				#1us;
				clkref_enable = 1'b0;
				#4us;
				check_timebase_state(PLL_HOLD, 0, 1);
				#500us;
				check_timebase_state(PLL_HOLD, 0, 1);
				transmit_pending = ~transmit_pending;
				#0.5us;
				check_timebase_state(NO_CLKREF);
				transmit_pending = 4'h0;
			`SVTEST_END
		end
		
		`SVTEST("Check no PLL hold if no transmission is pending and CLKREF is erroneous")
			clkref_enable = 1'b1;
			#300us;
			check_timebase_state(PLL_LOCKED);
			#1us;
			clkref_enable = 1'b0;
			#4us;
			check_timebase_state(NO_CLKREF);
		`SVTEST_END
			
		`SVTEST("Check auto clock trimming")
			int trim_value;
			use_oscillator_model_clock = 1'b1;
			clkref_enable = 1'b1;
			clock_period_half_clkref = 255000/(2*19) * 1ns;
			#10us;
			force i_timebase.test_auto_trim_en = 1'b1;
			#2ms;
			elip_read(ADDR_TIMEBASE_TRIM_OSC, trim_value);
			`FAIL_UNLESS_GREATER_OR_EQUAL(trim_value, 'h53-1)
			`FAIL_UNLESS_SMALLER_OR_EQUAL(trim_value, 'h53+1)
		`SVTEST_END
		release i_timebase.test_auto_trim_en;
		
	`SVUNIT_TESTS_END
		
	function automatic time get_frequency(time half_period);
		time temp;
		temp = 1s/(2*half_period);
		return temp;
	endfunction
	
	task check_timebase_state(timebase_state state, bit clkref=1'b0, bit pll=1'b0);
		case (state)
			NO_CLKREF: begin
				`FAIL_UNLESS_EQUAL(clkref_ok_monitor_signal, 0)
				`FAIL_UNLESS_EQUAL(pll_monitor_locked, 0)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_on, 0)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_hold, 0)
			end
			CLKREF_VALID: begin
				`FAIL_UNLESS_EQUAL(clkref_ok_monitor_signal, 1)
				`FAIL_UNLESS_EQUAL(pll_monitor_locked, 0)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_on, 1)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_hold, 0)
			end
			PLL_LOCKED: begin
				`FAIL_UNLESS_EQUAL(clkref_ok_monitor_signal, 1)
				`FAIL_UNLESS_EQUAL(pll_monitor_locked, 1)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_on, 1)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_hold, 0)
			end
			PLL_HOLD: begin
				`FAIL_UNLESS_EQUAL(clkref_ok_monitor_signal, clkref)
				`FAIL_UNLESS_EQUAL(pll_monitor_locked, pll)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_on, 1)
				`FAIL_UNLESS_EQUAL(timebase_io.pll_hold, 1)
			end
		endcase
	endtask

endmodule
