`define start_tmr_out_seq( _PIN_ )	begin \
tmr_out_seq#(tmr_out_checker_``_PIN_ )	_PIN_``_seq = new(); \
_PIN_``_seq.copy_references_from(this); \
`uvm_send( _PIN_``_seq ) \
end

class jtag_test_seq extends base_dsi_master_seq;
	
	localparam	real tfmin = 83.332;
	localparam	real tstep = 0.370370370;
	
	`ifndef GATE_LEVEL
		localparam string path_to_tmr_ana_dsi3_tx = "tmr_dsi[%1d].tmr_ana_dsi3_tx";
		localparam string path_to_tmr_ana_dsi3_rx = "tmr_dsi[%1d].tmr_ana_dsi3_rx";
	`else
		localparam string path_to_tmr_ana_dsi3_tx = "tmr_dsi_%1d__tmr_ana_dsi3_tx";
		localparam string path_to_tmr_ana_dsi3_rx = "tmr_dsi_%1d__tmr_ana_dsi3_rx";
	`endif
	
	`uvm_object_utils(jtag_test_seq)
	
	function new(string name = "");
		super.new("jtag_test");
	endfunction
	
	virtual task run_tests();
		log_sim_description("Basic testcase for JTAG and test", LOG_LEVEL_TOP);
		
		initialize();
		// FIXME: check_pll_hold_p52143_642();
		// FIXME: check_IPS_stuff_p52143_437();
		
		// FIXME: check_output_of_OSC_READY();
		check_dsi_uv_ov_at_high_temperature_p52143_472();
		// FIXME: check_all_pins_highz();
		check_scan();
		// FIXME: check_OTP_programming();
		check_tdo_unlatched_for_OTP_programming();
		check_JTAG_ID_p52143_446();
		check_test_top_dr_out_p52143_442();
		// FIXME: access_waveshape_using_pattern();
		// FIXME: test_p52143_455();
		// FIXME: test_ecps_pattern();
		initialize();
		
		check_tmr_ana();
		check_tmr_sel_val();
		elip_read_write_test();
		elip_read_write_ram_access_test();
		check_tmr_out();
		
		check_tmr_in(); //FIXME: add other input pins
		check_tmr_dig_supply();
		check_tmr_dig_dsi();
		check_tmr_dig_timebase();
		
		clock_autotrimming_test();
		`create_and_send(jtag_read_chip_id_seq)
		
		#1ms;
	endtask
	
	virtual task check_pll_hold_p52143_642();
		M52144A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
		int frequency_clkpll;
        log_sim_description("Check PLL hold (P52143-642)", LOG_LEVEL_SEQUENCE);
		initialize();
		enable_ecps_pattern();
		wrapper_class.run_test_top_TM_IC_INIT();
        log_sim_description("switch to PLL and measure PLL clock frequency", LOG_LEVEL_OTHERS);
		wrapper_class.run_test_osc_TM_CLK_PLL_DIV();
		measure_frequency(frequency_clkpll, "clkpll");
		
        log_sim_description("set PLL_HOLD=1 and PLL_ON=1");
		wrapper_class.run_test_osc_TM_PLL_HOLD();
		#10us;
		
        log_sim_description("disable CLKREF", LOG_LEVEL_OTHERS);
//		3) CLKREF abschalten
		set_clock_ref(.freq(400000),.enable(1'b1));
		#10us;
		set_clock_ref(.enable(1'b0));
		#10us;
		
        log_sim_description("measure PLL clock frequency", LOG_LEVEL_OTHERS);
//		4) PLL Taktfrequenz ausmessen (muss gleich bleiben) 
		measure_frequency(frequency_clkpll, "clkpll");

        log_sim_description("reset PLL_HOLD to check for wrong frequency");
//		5) Gegenprobe
		set_clock_ref(.freq(480000),.enable(1'b1));
		wrapper_class.run_test_osc_TM_PLL_HOLD_reset();
		#10us;
		measure_frequency(frequency_clkpll, "clkpll");
		
//		6) reset everything		
		#50us;
		set_clock_ref(.enable(1'b1));
		wrapper_class.run_test_osc_TM_PLL_reset();
		disable_ecps_pattern();
		#100us;
		toggle_reset_and_tmode();
		initialize();
		#500us;
	endtask
	
//	virtual task check_IPS_stuff_p52143_437();
//		E52143A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
//		log_test("Check correct settings for IPS tests (P52143-437)");
//		initialize();
//		enable_ecps_pattern();
////		wrapper_class.execute(E52143A_pattern_pkg::test_top_TM_IC_INIT);
//		wrapper_class.run_test_top_TM_IC_INIT();
//		
////		wrapper_class.execute(E52143A_pattern_pkg::SET_VRR_0x04);
//		wrapper_class.run_SET_VRR_0x04();
////		wrapper_class.execute(E52143A_pattern_pkg::SET_ATB_VRR_NO_LOAD);
//		wrapper_class.run_SET_ATB_VRR_NO_LOAD();
//		#5us;
//		`uvm_info(this.get_type_name(), $sformatf("measure VRR(0x04) without load here"), UVM_INFO)
//		#5us;
////		wrapper_class.execute(E52143A_pattern_pkg::SET_ATB_VRR_INT_LOAD);
//		wrapper_class.run_SET_ATB_VRR_INT_LOAD();
//		#5us;
//		`uvm_info(this.get_type_name(), $sformatf("measure VRR(0x04) with load here"), UVM_INFO)
//		#5us;
////		wrapper_class.execute(E52143A_pattern_pkg::SET_ATB_VRR_NO_LOAD);
//		wrapper_class.run_SET_ATB_VRR_NO_LOAD();
////		wrapper_class.execute(E52143A_pattern_pkg::SET_VRR_0x0F);
//		wrapper_class.run_SET_VRR_0x0F();
//		#5us;
//		`uvm_info(this.get_type_name(), $sformatf("measure VRR(0x0F) without load here"), UVM_INFO)
//		#5us;
////		wrapper_class.execute(E52143A_pattern_pkg::SET_VRR_0x08);
//		wrapper_class.run_SET_VRR_0x08();
//		#5us;
//		`uvm_info(this.get_type_name(), $sformatf("measure VRR(0x08) without load here"), UVM_INFO)
//		#5us;
//		
////		wrapper_class.execute(E52143A_pattern_pkg::test_top_ATB_reset);
//		wrapper_class.run_test_top_ATB_reset();
////		wrapper_class.execute(E52143A_pattern_pkg::SET_ATB_VPP_INT_LOAD);
//		wrapper_class.run_SET_ATB_VPP_INT_LOAD();
//		#5us;
//		`uvm_info(this.get_type_name(), $sformatf("measure VPP with load here"), UVM_INFO)
//		#5us;
////		wrapper_class.execute(E52143A_pattern_pkg::VPP_LEVEL_TEST);
//		wrapper_class.run_VPP_LEVEL_TEST();
//		#5us;
//		`uvm_info(this.get_type_name(), $sformatf("VPP Level test"), UVM_INFO)
//		#5us;
//		`uvm_info(this.get_type_name(), $sformatf("VREF Level test"), UVM_INFO)
//		#5us;
////		wrapper_class.execute(E52143A_pattern_pkg::test_supply_ATB_IPS_VREF);
//		wrapper_class.run_test_supply_ATB_IPS_VREF();
////		wrapper_class.execute(E52143A_pattern_pkg::VREF_LEVEL_TEST);
//		#10us;
//		disable_ecps_pattern();
//		#100us;
//		toggle_reset_and_tmode();
//		initialize();
//		#100us;
//	endtask
	
//	virtual task check_output_of_OSC_READY();
//		E52143A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
//		time times[2];
//		log_test("Check output of OSC_READY (P52143-585)");
//
//		initialize();
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.SEL_RFC.set(49);
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.EN_RFC.set(1);
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.update(status);
//		#1us;
//		check_rfc(1'b1);
//		test_regmodel.TEST_SCAN.scan_registers.SCAN.DISABLE_OSC.write(status, 1);
//		#10us;
//		check_rfc(1'b0);
//		test_regmodel.TEST_SCAN.scan_registers.SCAN.DISABLE_OSC.write(status, 0);
//		#1us;
//		check_rfc(1'b0);
//		#50us;
//		check_rfc(1'b1);
//
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.SEL_RFC.set(32);
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.EN_RFC.set(1);
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.update(status);
//		//test_regmodel.TEST_TOP.TEST_TOP.TMR_DIG.SEL_SYNC.write(status, 1);
//		#1us;
//		check_rfc(1'b1);
//		test_regmodel.TEST_SCAN.scan_registers.SCAN.DISABLE_OSC.write(status, 1);
//		#1us;
//		check_rfc(1'b0);
//		test_regmodel.TEST_SCAN.scan_registers.SCAN.DISABLE_OSC.write(status, 0);
//		#1us;
//		check_rfc(1'b0);
//		#50us;
//		check_rfc(1'b1);
//		
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_DIG.SEL_SYNC.write(status, 0);
//		
//		log_subtest("Check output of OSC_READY (P52143-585) with pattern start");
//		enable_ecps_pattern();
//		times[0] = $time();
//		wrapper_class.run_test_osc_TM_CLK_ready_chk_0();
//		times[1] = $time();
//		#10us;
//		check_rfc(1'b0);
//		fork
//			wrapper_class.run_test_osc_TM_CLK_ready_chk_1();
//			begin
//				#((times[1]-times[0])/2);
//				#5us;
//				check_rfc(1'b0);
//			end
//		join
//		#1us;
//		check_rfc(1'b1);
//		#10us;
//		disable_ecps_pattern();
//		#100us;
//		toggle_reset_and_tmode();
//		initialize();
//	endtask
	
	virtual task check_dsi_uv_ov_at_high_temperature_p52143_472();
		log_sim_description("Check output of DSI UV and OV at overtemperature (P52143-472)", LOG_LEVEL_SEQUENCE);
		jtag_disable();
		set_temp(175, 1us);
		#100us;
		set_resb(0); // do new powerup
		#100us;
		set_resb(1);
		get_checker_config().enable_hardware_error_check = 1'b0;
		fork
			begin
				@(posedge rfc.D);
			end
			begin
				#3ms;
				`uvm_error(this.get_type_name(), $sformatf("Ic did not powerup in time"))
			end
			begin
				initialize();
				for (int channel=0; channel<project_pkg::DSI_CHANNELS; channel++) begin
					test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_DIG_DSI3.PREVENT_DEACTIVATION.write(status, 1);
				end
				test_regmodel.TEST_SUP.TEST_SUPPLY.TMR_DIG_SUPPLY.PREVENT_OVERTEMPERATURE_SWITCH_OFF.write(status, 1);
				regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1);
				regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 'hf);
				#3ms;
			end
		join_any
		disable fork;
		
		for (int synced = 0; synced < 2; synced++) begin
			log_sim_description($sformatf("Check output of DSI UV and OV at overtemperature with synced output=%1b (P52143-472)", synced), LOG_LEVEL_OTHERS);
			test_regmodel.TEST_TOP.TEST_TOP.TMR_DIG.SEL_SYNC.write(status, synced);
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				
				test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.SEL_INTB.set(35+(channel*5)); //UV
				test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.EN_INTB.set(1);
				test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.update(status);
				
				test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.SEL_RFC.set(36+(channel*5)); //OV
				test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.EN_RFC.set(1);
				test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.update(status);
				check_output_of_ov_and_uv(channel);
			end
		end 
		
		fork
			begin
				set_temp(25, 1us);
				#100us;
			end
			begin
                #50us;
				jtag_disable();
				#50us;
                regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1);
                regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 'hf);
				initialize();
			end
		join
		get_checker_config().enable_hardware_error_check = 1'b1;
	endtask
	
	virtual task check_output_of_ov_and_uv(int channel);
		check_intb(1'b0);
		check_rfc(1'b0);
		set_dsi_ov_for_channel(channel, 1);
		#5us;
		check_intb(1'b0);
		check_rfc(1'b1);
		set_dsi_ov_for_channel(channel, 0);
		#5us;
		check_intb(1'b0);
		check_rfc(1'b0);
		set_dsi_uv_for_channel(channel, 1);
		#5us;
		check_intb(1'b1);
		check_rfc(1'b0);
		set_dsi_uv_for_channel(channel, 0);
		#5us;
		check_intb(1'b0);
		check_rfc(1'b0);
	endtask
	
//	virtual task check_all_pins_highz();
//		E52143A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
//		log_test("Check all pins highz");
//		enable_ecps_pattern();
//		
//		wrapper_class.run_gpio_TM_PADS_HZ();
//		#1ms;
//		hdl_force("top_tb.th.i_dut_wrapper.enable_pattern", 1'b0);
//		#100us;
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.write(status, 0);
//		#100us;
//		jtag_disable();
//		#100us;
//		toggle_reset_and_tmode();
//		initialize();
//	endtask
	
	virtual task check_scan();
		log_sim_description("Check scan test", LOG_LEVEL_SEQUENCE);
		hdl_force("top_tb.th.i_dut_wrapper.xtop.XANA.i_supply.REG_DIS", 0);
		for (int i=0; i<16; i++) begin
			initialize();
			test_regmodel.TEST_SCAN.scan_registers.SCAN.SCAN.set(1);
			test_regmodel.TEST_SCAN.scan_registers.SCAN.VDD_RDIV_DIS.set(i[0]);
			test_regmodel.TEST_SCAN.scan_registers.SCAN.VDD_ILOAD_DIS.set(i[1]);
			test_regmodel.TEST_SCAN.scan_registers.SCAN.VDD_DIS.set(i[2]);
			test_regmodel.TEST_SCAN.scan_registers.SCAN.DISABLE_OSC.set(i[3]);
			test_regmodel.TEST_SCAN.scan_registers.SCAN.update(status);
            //FIXME: set Compression!
			#2us;
			check_outputs_for_scan(i[2], i[0], i[1], ~i[3]);
			jtag_disable();
			#20us;
		end
		hdl_release("top_tb.th.i_dut_wrapper.xtop.XANA.i_supply.REG_DIS");
	endtask
	
	virtual function void check_outputs_for_scan(logic expect_vddd_disable, logic expect_vdd_voltage_divider_disable, logic expect_vdd_load_disable, logic expect_osc_on );
		check_value(expect_vddd_disable, "O_VDD_DISABLE");
		check_value(expect_vdd_voltage_divider_disable, "O_VDD_VOLTAGE_DIVIDER_DISABLE");
		check_value(expect_vdd_load_disable, "O_VDD_LOAD_DISABLE");
		check_value(expect_osc_on, "O_OSC_ON");
		check_value(1'b1, "tmr_scan.scan");
	endfunction
	
	function void check_value(logic expected, string pin);
		uvm_hdl_data_t value;
		value = hdl_read({`STRING_OF(`xdig_path), ".", pin});
		if (value[0] != expected) begin
			`uvm_error(this.get_type_name(), $sformatf("%s is not correctly set! Got %1b, but expected %1b", pin, value[0], expected ))
		end
	endfunction
	
	virtual task check_test_top_dr_out_p52143_442();
		log_sim_description("Check TEST_TOP DR output shift (P52143-442)", LOG_LEVEL_SEQUENCE);
		check_test_top_register(ADDR_TEST_TOP_TMR_ANA, 1);
		check_test_top_register(ADDR_TEST_TOP_TMR_DIG, 7);
		check_test_top_register(ADDR_TEST_TOP_TMR_IN, 16'hffff);
		check_test_top_register(ADDR_TEST_TOP_TMR_OUT_CSB_SCK, 16'h3f3f);
		check_test_top_register(ADDR_TEST_TOP_TMR_OUT_MOSI_MISO, 16'h3f3f);
		check_test_top_register(ADDR_TEST_TOP_TMR_OUT_BFWB_SYNCB, 16'h3f3f);
		check_test_top_register(ADDR_TEST_TOP_TMR_OUT_DAB_INTB, 16'h3f82); // INTB is TDO thus writing the wrong value here will disable TDO output!!! 0x3f -> 0x82
		check_test_top_register(ADDR_TEST_TOP_TMR_OUT_RFC, 16'h003f);
	endtask
	
	virtual task check_test_top_register(int address, shortint value);
		jtag_tr	jtag;
		shortint	previous_dr_value;
		`uvm_do_on_with(jtag, m_jtag_master_agent.m_sequencer, {ir_length == 8; ir_value == local::address; dr_length == 16; dr_value[15:0] == local::value; init_jtag == 1'b0;})
		previous_dr_value = jtag.read_dr[15:0];
		#1us;
		`uvm_do_on_with(jtag, m_jtag_master_agent.m_sequencer, {ir_length == 8; ir_value == local::address; dr_length == 16; dr_value[15:0] == local::previous_dr_value; init_jtag == 1'b0;}) // reset content
		if (jtag.read_dr[15:0] != value) begin
			`uvm_error(this.get_type_name(), $sformatf("TEST_TOP.%s seems not to be connected to JTAG! Exp. 0x%4h but got 0x%4h", test_addresses[address], value , jtag.read_dr[15:0]))
		end
		
		#10us;
	endtask
	
	virtual task check_tdo_unlatched_for_OTP_programming();
		string path; 
		jtag_tr	jtag;
		log_sim_description("Check tdo unlatched for OTP programming", LOG_LEVEL_SEQUENCE);
        initialize();
		path = $sformatf("%s%s", `STRING_OF(`LOGIC_TOP_PATH) , ".i_test.i_test_control.i_otp_wrapper.u_otpwrap_l3_top.u_otpwrap_l2_cpu.u_otpwrap_l1_jtag.otp_rdy");
		`uvm_do_on_with(jtag, m_jtag_master_agent.m_sequencer, {ir_length == 8; ir_value == int'(8'ha0); dr_length == 16; dr_value[15:0] == 16'h0400; init_jtag == 1'b0;})
		#5us;
		check_intb(1'b1);
		#1us;
		hdl_force(path, 1'b1);
		#5us;
		check_intb(1'b1);
		#1us;
		hdl_force(path, 1'b0);
		#5us;
		check_intb(1'b0);
		#1us;
		hdl_force(path, 1'b1);
		#5us;
		check_intb(1'b1);
		#1us;
		hdl_force(path, 1'b0);
		#5us;
		check_intb(1'b0);
		#1us;
		hdl_release(path);
		#10us;
	endtask
	
//	virtual task check_OTP_programming();
//		E52143A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
//		log_test("ECPS simulation of OTP programming");
//		
//		enable_ecps_pattern();
//		
////		wrapper_class.execute(E52143A_pattern_pkg::OTP_WRITE_BIST);
//		#10ms;
//			
//		disable_ecps_pattern();
//		#100us;
//		toggle_reset_and_tmode();
//		initialize();
//	endtask
	
	virtual task check_JTAG_ID_p52143_446();
		jtag_tr	jtag;
		log_sim_description("Check JTAG ID", LOG_LEVEL_SEQUENCE);
        initialize();
		`uvm_do_on_with(jtag, m_jtag_master_agent.m_sequencer, {ir_length == 8; ir_value == int'(8'hfb); dr_length == 32; dr_value == '0; init_jtag == 1'b0;})
		#1us;
		if (jtag.read_dr[27:12] != 52144) begin
			`uvm_error(this.get_type_name(), $sformatf("Project of JTAG_ID is not correct! Exp. 52144 (0xCBAF) but got %5d (0x%4h)", jtag.read_dr[27:12], jtag.read_dr[27:12]))
		end
		if (jtag.read_dr[11:1] != {3'h0, "E"}) begin
			`uvm_error(this.get_type_name(), $sformatf("Manufacturer of JTAG_ID is not correct! Exp. 0x045 (=E) but got 0x%3h", jtag.read_dr[11:1]))
        end
        //FIXME: add sim:measure
		#1us;
	endtask
	
	virtual task check_p52143_346(); //FIXME: add test!!!
		jtag_tr	j;
		`uvm_do_on_with(j, m_jtag_master_agent.m_sequencer, {ir_length == 8; ir_value == int'(8'hA0); dr_length == 16; dr_value == 266'h0006; init_jtag == 1'b0;})
		`uvm_do_on_with(j, m_jtag_master_agent.m_sequencer, {ir_length == 8; ir_value == int'(8'hA1); dr_length == 16; dr_value == 266'h0000; init_jtag == 1'b0;})
		`uvm_do_on_with(j, m_jtag_master_agent.m_sequencer, {ir_length == 8; ir_value == int'(8'h15); dr_length == 16; dr_value == 266'h0008; init_jtag == 1'b0;})
	endtask
	
//	virtual task access_waveshape_using_pattern(); //FIXME: add checks!
//		E52143A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
//		log_test("ECPS simulation to access waveshape registers");
//		
//		enable_ecps_pattern();
//		
//		wrapper_class.run_SET_DSI_TX_DAC_00000();
//		wrapper_class.run_SET_DSI_TX_DAC_00001();
//		wrapper_class.run_SET_DSI_TX_DAC_00010();
//		wrapper_class.run_SET_DSI_TX_DAC_00100();
//		wrapper_class.run_SET_DSI_TX_DAC_01000();
//		wrapper_class.run_SET_DSI_TX_DAC_10000();
//			
//		disable_ecps_pattern();
//		#100us;
//		toggle_reset_and_tmode();
//		#1ms;
//	endtask
	
//	virtual task test_p52143_455();
//		E52143A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
//		log_test("ECPS simulation for Jira Issue P52143-455");
//		
//		enable_ecps_pattern();
//		
//		#10us;
//		wrapper_class.run_test_top_TM_IC_INIT();
//		wrapper_class.run_SET_CLDO_STD();
//		wrapper_class.run_test_dsi_TM_DSI_TX_PIN();
//		#100us;
//		toggle_sdi();
//		#500us;
//		wrapper_class.run_test_top_TM_IC_INIT();
//		wrapper_class.run_SET_CLDO_MAX();
//		wrapper_class.run_test_dsi_TM_DSI_TX_PIN();
//		#100us;
//		toggle_sdi();
//		#100us;
//		toggle_reset_and_tmode();
//		
//		wrapper_class.run_test_top_TM_IC_INIT();
//		wrapper_class.run_SET_CLDO_STD();
//		wrapper_class.run_test_dsi_TM_DSI_TX_PIN();
//		#100us;
//		toggle_reset_and_tmode();
//		
//		wrapper_class.run_test_top_TM_IC_INIT();
//		wrapper_class.run_SET_CLDO_MAX();
//		wrapper_class.run_test_dsi_TM_DSI_TX_PIN();
//		#100us;
//		toggle_sdi();
//		
//		disable_ecps_pattern();
//		#1ms;
//	endtask
	
	virtual task toggle_reset_and_tmode();
		#100us;
		set_resb(0);
		jtag_disable();
		#100us;
		set_resb(1);    
		#1ms;
		jtag_enable();
		#100us;
	endtask
	
	virtual task toggle_sdi();
		apply_SDI(1'b1);
		apply_SDI(1'b0);
		apply_SDI(1'b1);
		apply_SDI(1'b0);
	endtask
	
	virtual task apply_SDI(bit expected);
		m_spi_agent.m_config.vif.SDI = expected;
		#8us;
		for (int channel=0; channel<project_pkg::DSI_CHANNELS; channel++) begin
			check_output_of_channel(channel, expected);
		end
	endtask
	
//	virtual task test_ecps_pattern();
//		E52143A_pattern_wrapper	wrapper_class = get_pattern_wrapper();
//		
//		enable_ecps_pattern();
//		#10us;
//		wrapper_class.run_test_top_TM_IC_INIT();
//		#500us;
//		disable_ecps_pattern();
//		#100us;
//		
//		initialize();
//		
//		/*
//		 * write TEST_TOP.TMR_DIG 0 {USE_JTAG=1}
//		 * write TEST_TOP.TMR_OUT_RFC 0 {SEL_RFC=2, EN_RFC=1}
//		 * write TEST_SUP.TMR_DIG_SUPPLY 0 {PREVENT_OVERTEMPERATURE_SWITCH_OFF=1}
//		 * write TEST_DSI_0.TMR_DIG_DSI3 0 {PREVENT_DEACTIVATION=1}
//		 * write TEST_DSI_1.TMR_DIG_DSI3 0 {PREVENT_DEACTIVATION=1}
//		 * write TEST_DSI_2.TMR_DIG_DSI3 0 {PREVENT_DEACTIVATION=1}
//		 * write TEST_DSI_3.TMR_DIG_DSI3 0 {PREVENT_DEACTIVATION=1}
//		 * write SUPPLY.IO_CTRL 0 {HICUR=1}
//		 * write TEST_TOP.TMR_ANA 0 {ENABLE_ATB=1}
//		 * */
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_DIG.USE_JTAG.set(1);
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_DIG.update(status);
//		
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.EN_RFC.set(1);
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.SEL_RFC.set(2);
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.update(status);
//		
//		test_regmodel.TEST_SUP.TEST_SUPPLY.TMR_DIG_SUPPLY.PREVENT_OVERTEMPERATURE_SWITCH_OFF.write(status, 1);
//		
//		for (int i=0; i<4; i++) begin
//			test_regmodel.TEST_DSI[i].TEST_DSI.TMR_DIG_DSI3.PREVENT_DEACTIVATION.write(status, 1);
//		end
//		
//		test_regmodel.TEST_TOP.TEST_TOP.TMR_ANA.write(status, 0);
//		
//		#100us;
//		jtag_disable();
//		#100us;
//	endtask
	
//	function E52143A_pattern_wrapper get_pattern_wrapper();
//		E52143A_pattern_wrapper	wrapper_class;
//		if (!uvm_config_db#(E52143A_pattern_wrapper)::get(m_sequencer, "", "pattern_wrapper", wrapper_class))
//			`uvm_error(get_type_name(), "Unable to get pattern wrapper from config DB!")
//		return wrapper_class;				
//	endfunction
	
	virtual task initialize();
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b0;
		jtag_enable_with_tdo(1'b1);
		#5us;
	endtask
	
	virtual task check_tmr_sel_val();
		log_sim_description("check TMR_SEL/_VAL", LOG_LEVEL_SEQUENCE);
		check_tmr_sel_val_dsi();
		check_tmr_sel_val_timebase();
	endtask
	
	virtual task check_tmr_sel_val_timebase();
		ral_reg_TEST_OSC_TMR_SEL_TB	tmr_sel = test_regmodel.TEST_OSC.TEST_OSC.TMR_SEL_TB;
		ral_reg_TEST_OSC_TMR_VAL_TB	tmr_val = test_regmodel.TEST_OSC.TEST_OSC.TMR_VAL_TB;
		log_sim_description($sformatf("check TMR_SEL/_VAL time base"), LOG_LEVEL_OTHERS);
		tmr_sel.set(0);	tmr_val.set(0);
		check_tmr_sel_val_register_with_signal(tmr_sel.PLL_HOLD, tmr_val.PLL_HOLD, "O_PLL_HOLD");
		tmr_sel.set(0);	tmr_val.set(0);
		check_tmr_sel_val_register_with_signal(tmr_sel.PLL_ON, tmr_val.PLL_ON, "O_PLL_ON");
        logger.log_sim_check(tmr_sel.get_name(), .status("PASS"));
        logger.log_sim_check(tmr_val.get_name(), .status("PASS"));
	endtask
	
	virtual task check_tmr_sel_val_dsi();
		ral_reg_TEST_DSI_TMR_SEL_DSI3	tmr_sel;
		ral_reg_TEST_DSI_TMR_VAL_DSI3	tmr_val;
		for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			tmr_sel = test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_SEL_DSI3;
			tmr_val = test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_VAL_DSI3;
			log_sim_description($sformatf("check TMR_SEL/_VAL DSI on channel %1d", channel), LOG_LEVEL_OTHERS);
			tmr_sel.set(0);	tmr_val.set(0);
			check_tmr_sel_val_register_with_signal(tmr_sel.HVCASC_ON, tmr_val.HVCASC_ON, $sformatf("O_DSI_TX_HVCASC_ON[%1d]",channel));
			tmr_sel.set(0);	tmr_val.set(0);
			check_tmr_sel_val_register_with_signal(tmr_sel.RX_ON, tmr_val.RX_ON, $sformatf("O_DSI_RX_ON[%1d]",channel));
			tmr_sel.set(0);	tmr_val.set(0);
			check_tmr_sel_val_register_with_signal(tmr_sel.RX_TXN, tmr_val.RX_TXN, $sformatf("O_DSI_RX_TXN[%1d]",channel));
			tmr_sel.set(0);	tmr_val.set(0);
			check_tmr_sel_val_register_with_signal(tmr_sel.TX_ON, tmr_val.TX_ON, $sformatf("O_DSI_TX_ON[%1d]",channel));
			//			tmr_sel.set(0);	tmr_val.set(0);
			//			check_tmr_sel_val_register_with_signal(tmr_sel.TX, tmr_val.TX, $sformatf("O_DSI_TX_DATA[%1d]",channel));
            logger.log_sim_check(tmr_sel.get_name(), .status("PASS"));
            logger.log_sim_check(tmr_val.get_name(), .status("PASS"));
		end
	endtask
	
	virtual task check_tmr_sel_val_register_with_signal(uvm_reg_field tmr_sel_field, uvm_reg_field tmr_val_field, string port_name);
		string path = { `STRING_OF(`xdig_path) , ".", port_name};
		int value;
		value = get_value_from_path(path);
		check_path_for_value(path, value);
		
		tmr_val_field.write(status, ~value);
		#1us;
		check_path_for_value(path, value);
		
		tmr_val_field.write(status, 0);
		tmr_sel_field.write(status, 1'b1);
		#1us;
		check_path_for_value(path, 0);
		
		for (int i=0; i < tmr_val_field.get_n_bits(); i++) begin
			tmr_val_field.write(status, 1<<i);
			#1us;
			check_path_for_value(path, 1<<i);
		end
		
		tmr_val_field.write(status, '1);
		tmr_sel_field.write(status, 1'b0);
		#1us;
		check_path_for_value(path, value);
	endtask
	
	virtual task check_tmr_ana();
		log_sim_description("check TMR_ANA", LOG_LEVEL_SEQUENCE);
		check_tmr_ana_supply();
		check_tmr_ana_osc();
		check_tmr_ana_dsi();
	endtask
	
	virtual task check_tmr_ana_supply();
		log_sim_description("check TMR_ANA_SUP", LOG_LEVEL_OTHERS);
		check_tmr_ana_register_with_signal(test_regmodel.TEST_SUP.TEST_SUPPLY.TMR_ANA_SUPPLY, "O_ATST_SUP");
		log_sim_description("check TMR_ANA_TEMP_SENSOR", LOG_LEVEL_OTHERS);
		check_tmr_ana_register_with_signal(test_regmodel.TEST_SUP.TEST_SUPPLY.TMR_ANA_TEMP_SENSOR, "O_ATST_TEMP_SENSOR");
		log_sim_description("check TMR_ANA_OTP", LOG_LEVEL_OTHERS);
		check_tmr_ana_register_with_signal(test_regmodel.TEST_SUP.TEST_SUPPLY.TMR_ANA_OTP, "O_ATST_OTP");
	endtask
	
	virtual task check_tmr_ana_osc();
		log_sim_description("check TMR_ANA_TB_OSC", LOG_LEVEL_OTHERS);
		check_tmr_ana_register_with_signal(test_regmodel.TEST_OSC.TEST_OSC.TMR_ANA_TB_OSC, "O_ATST_OSC");
		log_sim_description("check TMR_ANA_TB_PLL", LOG_LEVEL_OTHERS);
		check_tmr_ana_register_with_signal(test_regmodel.TEST_OSC.TEST_OSC.TMR_ANA_TB_PLL, "O_ATST_PLL");
	endtask
	
	virtual task check_tmr_ana_dsi();
		for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			log_sim_description($sformatf("check TMR_ANA_DSI_TX[%1d]",channel), LOG_LEVEL_OTHERS);
			check_tmr_ana_register_with_signal(test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_ANA_DSI3_TX, $sformatf(path_to_tmr_ana_dsi3_tx,channel));
			log_sim_description($sformatf("check TMR_ANA_DSI_RX[%1d]",channel), LOG_LEVEL_OTHERS);
			check_tmr_ana_register_with_signal(test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_ANA_DSI3_RX, $sformatf(path_to_tmr_ana_dsi3_rx,channel));
		end
	endtask
	
	virtual task check_tmr_ana_register_with_signal(uvm_reg tmr_register, string port_name);
		check_path_for_value({`STRING_OF(`xdig_path), ".", port_name}, 0);
		for (int i=0; i<get_used_bits_of_register(tmr_register); i++) begin
			tmr_register.write(status, 1<<i);
			#1us;
			check_path_for_value({`STRING_OF(`xdig_path), ".", port_name}, (1<<i));
		end
		tmr_register.write(status, 0);
		#1us;
		check_path_for_value({`STRING_OF(`xdig_path), ".", port_name}, 0);
        logger.log_sim_check(tmr_register.get_name(), .status("PASS"));
	endtask
	
	virtual function void check_path_for_value(string path, int expected_value);
		int value;
		value = int'(hdl_read(path));
		if (value != expected_value) begin
			`uvm_error(this.get_type_name(), $sformatf("Output at %s is NOT correct! Expected %h but got %h", path, expected_value, value))
		end
		else begin
			`uvm_info(this.get_type_name, $sformatf("Output at %s is correct! Expected %h and got %h", path, expected_value, value), UVM_HIGH)
		end
	endfunction
	
	virtual function int get_value_from_path(string path);
		int value;
		value = int'(hdl_read(path));
		return value;
	endfunction
	
	virtual function int get_used_bits_of_register(uvm_reg register);
		uvm_reg_field fields[$];
		int bits = 0;
		register.get_fields(fields);
		foreach(fields[i]) begin
			bits += fields[i].get_n_bits();
		end
		return bits;
	endfunction
	
	virtual task elip_read_write_test();
		jtag_write_elip_seq elip_write_seq;
		jtag_read_elip_seq elip_read_seq;
		
		log_sim_description("JTAG elip register read/write test", LOG_LEVEL_SEQUENCE);
		#100us;
		
		repeat(10) begin
			logic[10:0] value = 11'($urandom());
			`uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == ADDR_DSI_COMMON_CRM_TIME; data == 32'(value); init == 1;})
			#1us;
			`uvm_do_on_with(elip_read_seq, m_jtag_master_agent.m_sequencer, {address == ADDR_DSI_COMMON_CRM_TIME; init == 1;})
			if(elip_read_seq.read_value != 64'(value)) `uvm_error(this.get_type_name(), $sformatf("unexpected value for JTAG elip read/write, expected %04h, got %04h", value, elip_read_seq.read_value))
			#1us;
		end
		#100us;
	endtask
	
	virtual task elip_read_write_ram_access_test();
		shortint count = 16'd100;
		log_sim_description("JTAG elip RAM read/write of first and last 10 RAM cells", LOG_LEVEL_SEQUENCE);
		#100us;
		
			// write/read first 'count' RAM addresses
		log_sim_description($sformatf("check JTAG elip RAM access to first %0d addresses", count), LOG_LEVEL_OTHERS);
		for(int addr=int'(project_pkg::BASE_ADDR_RAM); addr < int'(project_pkg::BASE_ADDR_RAM + count); addr++) begin
			elip_write_read_check(addr);
		end
		// write/read last 'count' RAM addresses
		log_sim_description($sformatf("check JTAG elip RAM access to last %0d addresses", count), LOG_LEVEL_OTHERS);
		for(int addr=int'(project_pkg::BASE_ADDR_RAM + project_pkg::SIZE_RAM - 16'd1); addr > int'(project_pkg::BASE_ADDR_RAM + project_pkg::SIZE_RAM - count); addr--) begin
			elip_write_read_check(addr);
		end
		
		#100us;
	endtask
	
	virtual task elip_write_read_check(int addr);
		jtag_write_elip_seq elip_write_seq;
		jtag_read_elip_seq elip_read_seq;
		logic[15:0] value = 16'($urandom());
		
		`uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == addr; data == 32'(value); init == 1;})
		#1us;
		`uvm_do_on_with(elip_read_seq, m_jtag_master_agent.m_sequencer, {address == addr; init == 1;})
		if(elip_read_seq.read_value != 64'(value)) `uvm_error(this.get_type_name(), $sformatf("unexpected value for JTAG read/write at address x%0h, expected %04h, got %04h", addr, value, elip_read_seq.read_value))
		#1us;
	endtask
	
	virtual task clock_autotrimming_test();
		log_sim_description("oszillator auto trimming test", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_hardware_error_check = 1'b0;
		set_clock_ref(.enable(0));
		#100us;
		
		jtag_enable_with_tdo();
		
		set_trim_to_0();
		
		check_clock_trimming(22_000_000);
		check_clock_trimming(16_000_000);
		check_clock_trimming(18_000_000);
		
		set_clock_ref(.freq(500000));
		get_checker_config().enable_hardware_error_check = 1'b1;
	endtask
	
	virtual task check_clock_trimming(int frequency);
		shortint	trim_value;
		log_sim_description($sformatf("automatic trimming of oscillator to %2.4f",frequency/1000000.0), LOG_LEVEL_OTHERS);
		
		set_clock_ref(.freq((frequency)/255));
		#20us;
		set_autotrim(1'b1);
		#2ms;
		read_osc_trim_value(trim_value);
		check_trim_value_for(trim_value, frequency);
		set_autotrim(1'b0);
	endtask
	
	virtual task set_autotrim(bit enable);
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.CLK_AUTO_TRIM_EN.write(status, enable);
	endtask
	
	virtual task read_osc_trim_value(output shortint trim_value);
		uvm_reg_data_t value;
		regmodel.Timebase.time_base_registers.TRIM_OSC.read(status, value);
		trim_value = value[15:0];
	endtask
	
	virtual task set_trim_to_0();
		jtag_write_elip_seq	write_seq;
		`uvm_do_on_with(write_seq, m_jtag_master_agent.m_sequencer, {address == ADDR_TIMEBASE_TRIM_OSC; data == 0; init == 0;})
	endtask
	
	virtual function void check_trim_value_for(shortint trim_value, int frequency);
		shortint temp_trim_value = shortint'((tfmin - (1000000000.0/frequency))/tstep);
		if ((trim_value < temp_trim_value -16'd1) || (trim_value > temp_trim_value+16'd1)) begin
			`uvm_error(this.get_type_name(), $sformatf("Trim value=%4h(%5d) for %2.4fMHz is not OK. Expected %1d +/-1", trim_value, trim_value, frequency/1000000.0, temp_trim_value))
		end
		else begin
			`uvm_info(this.get_type_name(), $sformatf("Trim value=%4h(%5d) for %2.4fMHz", trim_value, trim_value, frequency/1000000.0), UVM_HIGH)
		end
	endfunction
	
	virtual task check_tmr_in();
		log_sim_description($sformatf("check TMR_IN"), LOG_LEVEL_SEQUENCE);
		
		for (int tmr_in = 0; tmr_in < 4; tmr_in++) begin
			case (tmr_in)
				0: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_0.write(status, 1);
				1: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_1.write(status, 1);
				2: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_2.write(status, 1);
				3: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_3.write(status, 1);
			endcase
			for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				log_sim_description($sformatf("check TMR_IN for pin CSB for tmr_in=%1d and channel=%1d", tmr_in, channel), LOG_LEVEL_OTHERS);
				
				test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_VAL_DSI3.RX_TXN.write(status, 1'b0);
				test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_SEL_DSI3.RX_TXN.write(status, 1'b1);
				test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_IN_DSI3.tmr_in_tx.write(status, (tmr_in+1));
				
				check_output_of_channel(channel, 1'b1);
				apply_CSN(channel, 1'b0);
				apply_CSN(channel, 1'b1);
				apply_CSN(channel, 1'b0);
				apply_CSN(channel, 1'b1);
				
				test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_IN_DSI3.tmr_in_tx.write(status, 0);
				test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_SEL_DSI3.RX_TXN.write(status, 1'b0);
			end
			case (tmr_in)
				0: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_0.write(status, 0);
				1: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_1.write(status, 0);
				2: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_2.write(status, 0);
				3: test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.tmr_in_3.write(status, 0);
			endcase
            logger.log_sim_check(test_regmodel.TEST_TOP.TEST_TOP.TMR_IN.get_name(), .status("PASS"));
		end
	endtask
	
	virtual task apply_CSN(int channel, bit expected);
		m_spi_agent.m_config.vif.CSN = expected;
		#8us;
		check_output_of_channel(channel, expected);
	endtask
	
	virtual function void check_output_of_channel(int channel, bit expected);
		dsi3_master_config	_config = get_dsi3_master_config(channel);
		if (_config.vif.cable.Voltage != expected) begin
			`uvm_error(this.get_type_name(), $sformatf("Output of channel %1d is not expected! Got %1b but expected %1b", channel, _config.vif.cable.Voltage, expected))
		end
	endfunction
	
	virtual task check_tmr_dig_supply();
		log_sim_description("check TMR_DIG_SUPPLY", LOG_LEVEL_SEQUENCE);
		log_sim_description($sformatf("prevent overtemperature switch off"), LOG_LEVEL_OTHERS);
		get_checker_config().enable_hardware_error_check = 1'b0;
		
		test_regmodel.TEST_SUP.TEST_SUPPLY.TMR_DIG_SUPPLY.PREVENT_OVERTEMPERATURE_SWITCH_OFF.write(status, 1'b1);
		set_temp(180, 10us);
		#20us;
		check_ldo(1'b1);
		check_dsi(2'b11);
		test_regmodel.TEST_SUP.TEST_SUPPLY.TMR_DIG_SUPPLY.PREVENT_OVERTEMPERATURE_SWITCH_OFF.write(status, 1'b0);
		#5us;
		check_dsi(2'b00);
		set_temp(25, 10us);
		#20us;
		regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 4'hf);
		check_ldo(1'b1);
		check_dsi(2'b11);
		
		get_checker_config().enable_hardware_error_check = 1'b1;
        log_sim_check($sformatf("TMR_DIG_SUPPLY"), , "PASS");
	endtask
	
	virtual task check_ldo(bit expected);
		uvm_reg_data_t	read_value;
		regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.read(status, read_value);
		if (read_value[0] != expected) begin
			`uvm_error(this.get_type_name(), $sformatf("LDO is not enabled! Got %1b, but expected %1b", read_value[0], expected))
		end
	endtask
	
	virtual task check_dsi(bit[project_pkg::DSI_CHANNELS-1:0] expected);
		uvm_reg_data_t	read_value;
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.read(status, read_value);
		if (read_value[project_pkg::DSI_CHANNELS-1:0] != expected) begin
			`uvm_error(this.get_type_name(), $sformatf("DSI is not enabled! Got %2b, but expected %2b", read_value[project_pkg::DSI_CHANNELS-1:0], expected))
		end
		for (int i=0; i<project_pkg::DSI_CHANNELS; i++) check_output_of_channel(i, expected[i]);
	endtask
	
	virtual task check_tmr_dig_dsi();
		log_sim_description("check TMR_DIG_DSI", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_hardware_error_check = 1'b0;
		for (int channel=0; channel<project_pkg::DSI_CHANNELS; channel++) begin
			log_sim_description($sformatf("prevent overvoltage switch off for channel %1d", channel), LOG_LEVEL_OTHERS);
			test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_DIG_DSI3.PREVENT_DEACTIVATION.write(status, 1'b1);
			set_dsi_ov_for_channel(channel, 1'b1);
			#7ms;
			check_dsi(2'b11);
			test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_DIG_DSI3.PREVENT_DEACTIVATION.write(status, 1'b0);
			#10us;
			check_dsi(2'b11 ^ (1<<channel));
			set_dsi_ov_for_channel(channel, 1'b0);
			#7ms;
			regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 4'hf);
			#10us;
			check_dsi(2'b11);
			
			log_sim_description($sformatf("prevent undervoltage switch off for channel %1d", channel), LOG_LEVEL_OTHERS);
			test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_DIG_DSI3.PREVENT_DEACTIVATION.write(status, 1'b1);
			set_dsi_uv_for_channel(channel, 1'b1);
			#7ms;
			check_dsi(2'b11);
			test_regmodel.TEST_DSI[channel].TEST_DSI.TMR_DIG_DSI3.PREVENT_DEACTIVATION.write(status, 1'b0);
			#10us;
			check_dsi(2'b11 ^ (1<<channel));
			set_dsi_uv_for_channel(channel, 1'b0);
			#7ms;
			regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 4'hf);
			#10us;
			check_dsi(2'b11);
		end
		get_checker_config().enable_hardware_error_check = 1'b1;
        log_sim_check($sformatf("TMR_DIG_DSI3"), , "PASS");
	endtask
	
	virtual task check_tmr_dig_timebase();
		jtag_write_elip_seq elip_write_seq;
		int frequency_clkosc, frequency_clkpll;

		log_sim_description("check TMR_DIG_TB", LOG_LEVEL_SEQUENCE);
		
		`uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == addresses_pkg::ADDR_TIMEBASE_TRIM_OSC; data == 32'h40; init == 0;}) // change trimming
		
		rfc_out(20); // output clkosc at RFC 
		#100us;
		measure_frequency(frequency_clkosc, "clkosc");
		
		rfc_out(21); // output clkpll at RFC
		#100us;
		measure_frequency(frequency_clkpll, "clkpll");

		rfc_out(22); // output clksys at RFC
		check_switched_clock(1'b0, frequency_clkosc, "switched sysclk (OSC)");
		check_switched_clock(1'b1, frequency_clkpll, "switched sysclk (PLL)");
		check_switched_clock(1'b0, frequency_clkosc, "switched sysclk (OSC)");
		check_switched_clock(1'b1, frequency_clkpll, "switched sysclk (PLL)");
		
		// restore defaults
		`uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == addresses_pkg::ADDR_TIMEBASE_TRIM_OSC; data == 32'h4b; init == 0;}) // change trimming
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.CLKSW_TST_EN.write(status, 0);
	endtask
	
	virtual task check_switched_clock(logic clksw_tst_sel, int expected_frequency, string name);
		int frequency_switched;
		clksw(clksw_tst_sel); 
		#100us;
		measure_frequency(frequency_switched, name);
		if((frequency_switched > (expected_frequency + 20000)) || (frequency_switched < (expected_frequency - 20000))) 
			`uvm_error(this.get_type_name(), $sformatf("unexpected frequency at RFC, expected %7.4fMHz, got %7.4fMHz", expected_frequency/1_000_000.0, frequency_switched/1_000_000.0))
	endtask
	
	virtual task rfc_out(logic[5:0] selection);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.EN_RFC.set(1);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.SEL_RFC.set(selection);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.update(status);
	endtask
	
	virtual task clksw(logic selection);
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.CLKSW_TST_EN.set(1);
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.CLKSW_TST_SEL.set(selection);
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.update(status);
	endtask
	
	virtual task measure_frequency(output int frequency, input string name);
		fork
			begin
				realtime start_time;
				@(posedge rfc.D);
				start_time = $realtime();
				@(posedge rfc.D);
				frequency = int'(1.0s / ($realtime() - start_time));
				`uvm_info(this.get_type_name(), $sformatf("measured %s frequency is %7.3fMHz", name, frequency/1_000_000.0), UVM_INFO);
			end
			begin // timeout
				#100us;
				`uvm_error(this.get_type_name(), $sformatf("failed to measure frequency, there was no posedge"))
			end
		join_any
		disable fork;
		#1us;
	endtask
	
	task check_tmr_out();
		`start_tmr_out_seq(INTB)
		`start_tmr_out_seq(RFC)
		
		`start_tmr_out_seq(SCK)
		`start_tmr_out_seq(MISO)
		`start_tmr_out_seq(CSB)
		`start_tmr_out_seq(MOSI)
		
		
		`start_tmr_out_seq(DAB)
		`start_tmr_out_seq(SYNCB)
		`start_tmr_out_seq(BFWB)
	endtask
	
endclass
