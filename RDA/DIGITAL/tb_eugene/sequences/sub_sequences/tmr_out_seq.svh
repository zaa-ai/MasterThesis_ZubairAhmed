class paths_object;
	protected string paths[$][2];
	
	static paths_object _paths;
	
	function new();
		add_value("0" , "static LOW");
		add_value("1" , "static HIGH");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_test.i_test_control.i_jtag_tap.tdo_latch"} , "TDO");
		// GPIO
		add_value({`STRING_OF(`xdig_path), ".I_CSB"} , "CSB");
		add_value({`STRING_OF(`xdig_path), ".I_SCK"} , "SCK");
		add_value({`STRING_OF(`xdig_path), ".I_SDO"} , "MISO");
		add_value({`STRING_OF(`xdig_path), ".I_SDI"} , "MOSI");
		add_value({`STRING_OF(`xdig_path), ".I_RFC"} , "RFC");
		add_value({`STRING_OF(`xdig_path), ".I_INTB"} , "INTB");
		add_value({`STRING_OF(`xdig_path), ".I_DAB"} , "DAB");
		add_value({`STRING_OF(`xdig_path), ".I_BFWB"} , "BFWB");
		add_value({`STRING_OF(`xdig_path), ".I_SYNCB"} , "SYNCB");
		add_value({`STRING_OF(`xdig_path), ".I_RESB"} , "RESB");
		// supply
		add_value({`STRING_OF(`xdig_path), ".I_OT_WARN"} , "OT_WARN");
		add_value({`STRING_OF(`xdig_path), ".I_OT_ERROR"} , "OT_ERROR");
		add_value({`STRING_OF(`xdig_path), ".I_VCC_OK"} , "VCC_OK");
		add_value({`STRING_OF(`xdig_path), ".I_LDO_OK"} , "LDO_OK");
		add_value({`STRING_OF(`xdig_path), ".I_VRR_OK"} , "VRR_OK");
		// oscillator
		add_value({`STRING_OF(`xdig_path), ".I_CLKREF"} , "CLKREF filtered");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_timebase.i_clkref_divider.o_clkref_div"} , "CLKREF divided");
		add_value({`STRING_OF(`xdig_path), ".I_CLKOSC"} , "CLKOSC");
		add_value({`STRING_OF(`xdig_path), ".I_CLKPLL"} , "CLKPLL");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_test.i_test_control.switched_clock"} , "System clock");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_timebase.i_clk_div_clkosc.clk_divided"} , "CLKOSC divided");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_timebase.i_clk_div_clkpll.clk_divided"} , "CLKPLL divided");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_timebase.i_clk_div_clksys.clk_divided"} , "CLKSYS divided");
		add_value({`STRING_OF(`xdig_path), ".I_CLKPLL_DIV"} , "I_CLKPLL_DIV");
		add_value({`STRING_OF(`xdig_path), ".I_PLL_DOWN_MON"} , "I_PLL_DOWN_MON");
		add_value({`STRING_OF(`xdig_path), ".I_PLL_UP_MON"} , "I_PLL_UP_MON");
		add_value({`STRING_OF(`xdig_path), ".I_PLL_LOCK_MON"} , "I_PLL_LOCK_MON");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_timebase.clkref_ok"} , "CLKREF ok");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), ".i_timebase.pll_locked"} , "PLL locked");
		add_value({`STRING_OF(`xdig_path), ".I_OSC_READY"} , "I_OSC_READY");
		// DSI
		for(int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			add_value($sformatf("%s%s[%1d]", `STRING_OF(`xdig_path), ".I_DSI_RXD1", i) , $sformatf("DSI%1d RXD1", i));
			add_value($sformatf("%s%s[%1d]", `STRING_OF(`xdig_path), ".I_DSI_RXD2", i) , $sformatf("DSI%1d RXD2", i));
			add_value($sformatf("%s%s[%1d]", `STRING_OF(`xdig_path), ".I_DSI_UVB" , i) , $sformatf("DSI%1d UV  ", i));
			add_value($sformatf("%s%s[%1d]", `STRING_OF(`xdig_path), ".I_DSI_OV"  , i) , $sformatf("DSI%1d OV  ", i));
			add_value($sformatf("%s%s[%1d]", `STRING_OF(`xdig_path), ".I_DSI_ICMP", i) , $sformatf("DSI%1d ICMP", i));
        end
        repeat (6) add_value("0", "nothing");
		add_value({`STRING_OF(`xdig_path), ".osc_ready_synced"} , "I_OSC_READY synced");
		add_value({`STRING_OF(`LOGIC_TOP_PATH), "..i_test.i_test_control.i_otp_wrapper.U_OTPWRAP_L3_TOP.U_OTPWRAP_L2_CPU.U_OTPWRAP_L1_JTAG.OTP_RDY"} , "OTP_READY");
		for(int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			add_value($sformatf("%s.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.i_dsi3_receive.chip_filtered.chip[0]", `STRING_OF(`LOGIC_TOP_PATH), i) , $sformatf("DSI%1d RXD1 filtered", i));
			add_value($sformatf("%s.i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.i_dsi3_receive.chip_filtered.chip[1]", `STRING_OF(`LOGIC_TOP_PATH), i) , $sformatf("DSI%1d RXD2 filtered", i));
        end
        repeat (4-project_pkg::DSI_CHANNELS) begin
            repeat(2)
                add_value("0", "nothing");
        end
	endfunction
	
	static function paths_object get();
		if (_paths == null)
			_paths = new();
		return _paths;
	endfunction
	
	protected function void add_value(string path, string name);
		string new_pair[2] = '{name, path};
		paths.push_back(new_pair);
	endfunction
	
	static function string get_name(int selected);
		paths_object p = get();
		return	p.paths[selected][0];
	endfunction
	
	static function string get_path(int selected);
		paths_object p = get();
		return	p.paths[selected][1];
	endfunction
	
endclass

class tmr_out_checker extends base_dsi_master_seq;
	
	protected uvm_reg_field	enable;
	protected uvm_reg_field	select;
	
	protected string pin_name = "NONE";
	protected bit is_jtag = 1'b0;
	protected bit is_jtag_tdo = 1'b0;
	
	`uvm_object_utils(tmr_out_checker)
	
	protected int selected;
	
	function new(string name = "tmr_out_checker");
		super.new(name);
	endfunction : new
	
	virtual function void apply_fields();
		`uvm_error(this.get_type_name(), "This function hast to be overridden by subclass!")
	endfunction
	
	virtual function void set_select(int selected);
		this.selected = selected;
	endfunction
	
	virtual task get_pin_value(output logic value);
		`uvm_error(this.get_type_name(), "DO NOT USE ME! Use my sub classes!")
		value = 1'b0;
	endtask
	
	virtual task check_pin_value(logic expected);
		logic	value;
		this.get_pin_value(value);
		
		if (value !== expected) begin
			`uvm_error(this.get_type_name(), $sformatf("Value at pin %s is not expected for %s (%1d)! Got %1b but expected %1b", get_pin_name(), paths_object::get_name(selected), selected, value, expected))
		end
	endtask
	
	virtual task check_selected();
		case (selected)
			0, 1: check_for_static(selected[0]);
            43,44,45,46,47,48, 55,56,57,58: check_for_static(1'b0);
			default: check_for_dynamic(selected);
        endcase
        log_sim_check($sformatf("Row %1d", selected), , "PASS");
	endtask
	
	virtual task check_for_dynamic(int selected);
		case (selected)
			18,19,20,21,22,23,24,25: begin
				check_for_clock(selected);
			end
			35, 40: check_for_A2D_signal(selected, 1'b1); // inverted
			default: check_for_A2D_signal(selected);
		endcase
		
	endtask
	
	virtual task check_for_clock(int selected);
		
		check_for_A2D_signal(selected);
		#500us;
		case (selected)
			18, 19: begin //FIXME: check CLKREF divider
				check_clock_frequency(500_000);
				set_clock_ref(490_000);
				check_clock_frequency(490_000);
				set_clock_ref(500_000);
			end
			20: check_clock_frequency(17_986_000);
			21, 22, 26: check_clock_frequency(18_000_000);
			23: check_clock_frequency(502_856);
			24, 25: check_clock_frequency(500_000);
		endcase
		#500us;
	endtask
	
	virtual task check_clock_frequency(int expected_frequency);
		fork
			begin
				realtime start_time, end_time;
				real frequency;
				int measured_frequency;
				#2us;
				get_posedge();
				start_time = $realtime();
				get_posedge();
				end_time = $realtime();
				frequency = 1.0s / (end_time - start_time);
				measured_frequency = int'(frequency);
//				$display("frequency is %7.3fMHz", frequency);
//				$display("start time is %t", start_time);
//				$display("  end time is %t", end_time);
				if ((measured_frequency + 10000 < expected_frequency) || (measured_frequency -10000 > expected_frequency)) begin
					`uvm_error(this.get_type_name(), $sformatf("measured clock frequency at pin %s is wrong! got %7.3fMHz but expected %7.3fMHz +- 0.01MHz", pin_name ,measured_frequency/1000000.0, expected_frequency/1000000.0))
				end
				else begin
					`uvm_info(this.get_type_name(), $sformatf("measured clock frequency is %7.3fMHz",measured_frequency/1000000.0), UVM_INFO);
				end
			end
			begin // timeout
				#100us;
				`uvm_error(this.get_type_name(), $sformatf("NO clock output"))
			end
		join_any
		disable fork;
		#1us;
	endtask
		
	virtual task get_posedge();
		`uvm_error(this.get_type_name(), "DO NOT USE ME! Use my sub classes!")
	endtask
	
	virtual task check_for_static(logic value);
		check_pin_value(value);
		#0.1us;
	endtask
	
	virtual task check_for_A2D_signal(int selected, bit inverted=1'b0);
		string path = paths_object::get_path(selected);
		// force selected -> 0
		hdl_force(path, 1'b0);
		#0.15us;
		check_pin_value(inverted);
		// force selecetd -> 1
		hdl_force(path, 1'b1);
		#0.15us;
		check_pin_value(~inverted);
		// release
		hdl_release(path);
	endtask
	
	virtual function string get_pin_name();
		return pin_name;
	endfunction
	
	virtual function uvm_reg_field get_enable_field();
		return enable;
	endfunction
	
	virtual function void set_enable_field(uvm_reg_field field);
		this.enable = field;
	endfunction
	
	virtual function uvm_reg_field get_select_field();
		return select;
	endfunction
	
	virtual function void set_select_field(uvm_reg_field field);
		this.select = field;
	endfunction
	
	virtual function bit is_jtag_pin();
		return is_jtag;
	endfunction
	
	virtual function bit is_jtag_tdo_pin();
		return is_jtag_tdo;
	endfunction
	
endclass

class tmr_out_checker_INTB extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_INTB)
	
	function new(string name = "tmr_out_checker_INTB");
		super.new(name);
		pin_name = "INTB";
		is_jtag = 1'b1;
		is_jtag_tdo = 1'b1;
	endfunction 
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.EN_INTB;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.SEL_INTB;		
	endfunction
	
	virtual task get_pin_value(output logic value);
		value = intb.D;
	endtask
	
	virtual task get_posedge();
		@(posedge intb.D);
	endtask
	
endclass

class tmr_out_checker_DAB extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_DAB)
	
	function new(string name = "tmr_out_checker_DAB");
		super.new(name);
		pin_name = "DAB";
		is_jtag = 1'b1;
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.EN_DAB;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.SEL_DAB;
	endfunction
	
	virtual task get_pin_value(output logic value);
		logic previous_value = m_jtag_master_agent.m_config.vif.TMS; 
		m_jtag_master_agent.m_config.vif.TMS = 1'bz;
		#1;
		value = dab.D;
		#1;
		m_jtag_master_agent.m_config.vif.TMS = previous_value;
	endtask
	
	virtual task get_posedge();
		@(posedge dab.D);
	endtask
	
endclass

class tmr_out_checker_RFC extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_RFC)
	
	function new(string name = "tmr_out_checker_RFC");
		super.new(name);
		pin_name = "RFC";
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.EN_RFC;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.SEL_RFC;
	endfunction
	
	virtual task get_pin_value(output logic value);
		value = rfc.D;
	endtask
	
	virtual task get_posedge();
		@(posedge rfc.D);
	endtask
endclass

class tmr_out_checker_SYNCB extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_SYNCB)
	
	function new(string name = "tmr_out_checker_SYNCB");
		super.new(name);
		pin_name = "SYNCB";
		is_jtag = 1'b1;
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_BFWB_SYNCB.EN_SYNCB;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_BFWB_SYNCB.SEL_SYNCB;
	endfunction
	
	virtual task get_pin_value(output logic value);
		logic	tdi;
		uvm_hdl_data_t _value;
		tdi = m_jtag_master_agent.m_config.vif.TDI;
		m_jtag_master_agent.m_config.vif.TDI = 1'bz;
		#1us;
		_value = hdl_read({`STRING_OF(`dut_wrapper_path),".xtop.SYNCB_P"});
		#1us;
		m_jtag_master_agent.m_config.vif.TDI = tdi;
		value = _value[0];
	endtask
	
	virtual task get_posedge();
		uvm_hdl_data_t _value;
		logic	tdi;
		tdi = m_jtag_master_agent.m_config.vif.TDI;
		m_jtag_master_agent.m_config.vif.TDI = 1'bz;
		
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SYNCB_P"});
		end while (_value[0] !== 1'b0);
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SYNCB_P"});
		end while (_value[0] === 1'b0);
		
		m_jtag_master_agent.m_config.vif.TDI = tdi;
	endtask
	
endclass

class tmr_out_checker_BFWB extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_BFWB)
	
	function new(string name = "tmr_out_checker_BFWB");
		super.new(name);
		pin_name = "BFWB";
		is_jtag = 1'b1;
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_BFWB_SYNCB.EN_BFWB;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_BFWB_SYNCB.SEL_BFWB;
	endfunction
	
	virtual task get_pin_value(output logic value);
		logic	previous_value = m_jtag_master_agent.m_config.vif.TCK;
		m_jtag_master_agent.m_config.vif.TCK = 1'bz;
		#1;
		value = bfwb.D;
		#1;
		m_jtag_master_agent.m_config.vif.TCK = previous_value;
	endtask
	
	virtual task get_posedge();
		@(posedge bfwb.D);
	endtask

endclass

class tmr_out_checker_CSB extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_CSB)
	
	function new(string name = "tmr_out_checker_CSB");
		super.new(name);
		pin_name = "CSB";
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_CSB_SCK.EN_CSB;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_CSB_SCK.SEL_CSB;
		spi.CSN = 1'bz;
	endfunction
	
	virtual task get_pin_value(output logic value);
		uvm_hdl_data_t _value;
		_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.CSB_P"});
		value = _value[0];
	endtask
	
	virtual task get_posedge();
		uvm_hdl_data_t _value;
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.CSB_P"});
		end while (_value[0] != 1'b0);
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.CSB_P"});
		end while (_value[0] == 1'b0);
	endtask
	
endclass

class tmr_out_checker_SCK extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_SCK)
	
	function new(string name = "tmr_out_checker_SCK");
		super.new(name);
		pin_name = "SCK";
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_CSB_SCK.EN_SCK;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_CSB_SCK.SEL_SCK;
	endfunction
	
	virtual task get_pin_value(output logic value);
		uvm_hdl_data_t _value;
		_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SCK_P"});
		value = _value[0];
	endtask
	
	virtual task get_posedge();
		uvm_hdl_data_t _value;
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SCK_P"});
		end while (_value[0] != 1'b0);
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SCK_P"});
		end while (_value[0] == 1'b0);
		
		//@(posedge spi_vif.SCK);
	endtask
	
endclass

class tmr_out_checker_MOSI extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_MOSI)
	
	function new(string name = "tmr_out_checker_MOSI");
		super.new(name);
		pin_name = "MOSI";
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_MOSI_MISO.EN_MOSI;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_MOSI_MISO.SEL_MOSI;
		spi.SDI = 1'bz;
	endfunction
	
	virtual task get_pin_value(output logic value);
		uvm_hdl_data_t _value;
		_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SDI_P"});
		value = _value[0];
	endtask
	
	virtual task get_posedge();
		uvm_hdl_data_t _value;
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SDI_P"});
		end while (_value[0] != 1'b0);
		do begin
			#10ps;
			_value = hdl_read({`STRING_OF(`dut_wrapper_path), ".xtop.SDI_P"});
		end while (_value[0] == 1'b0);
		//@(posedge spi_vif.SDI);
	endtask
	
endclass

class tmr_out_checker_MISO extends tmr_out_checker;
	
	`uvm_object_utils(tmr_out_checker_MISO)
	
	function new(string name = "tmr_out_checker_MISO");
		super.new(name);
		pin_name = "MISO";
	endfunction
	
	virtual function void apply_fields();
		enable = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_MOSI_MISO.EN_MISO;
		select = test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_MOSI_MISO.SEL_MISO;
	endfunction
	
	virtual task get_pin_value(output logic value);
		value = spi.SDO;
	endtask
	
	virtual task get_posedge();
		@(posedge spi.SDO);
	endtask
endclass


class tmr_out_seq #(type T=tmr_out_checker) extends base_dsi_master_seq;
	
	uvm_reg_field	enable;
	uvm_reg_field	select;
	
	T	_checker;
	
	`uvm_object_param_utils(tmr_out_seq)
	
	function new(string name = "tmr_out_seq");
		super.new(name);
	endfunction : new
	
	virtual task run_tests();
		_checker = new();
		_checker.copy_references_from(this);
		_checker.apply_fields();
		
		log_sim_description($sformatf("Check TMR_OUT for pad %s", _checker.get_pin_name()), LOG_LEVEL_SEQUENCE);
		enable = _checker.get_enable_field();
		select = _checker.get_select_field();
		
		initialize_again();
		
		for (int selected = 0; selected<project_pkg::TMR_OUT_TEST_VECTOR_WIDTH; selected++) begin
			_checker.set_select(selected);
			check_select(selected);
		end
		
		initialize_again();
		
	endtask
	
	virtual task initialize_again();
		jtag_disable();
		#1us;
		jtag_enable_with_tdo(1'b1);
		#5us;
	endtask
	
	virtual task jtag_enable_tdo_output();
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.EN_DAB.set(1'b0);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.SEL_DAB.set(0);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.EN_INTB.set(1'b1);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.SEL_INTB.set(2);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.update(status);
	endtask
	
	virtual task check_select(int tmr_out_select);
		logic	current_pin_value;
		log_sim_description($sformatf("Check TMR_OUT[%1d]( %s ) for pad %s", tmr_out_select, paths_object::get_name(tmr_out_select) , _checker.get_pin_name()), LOG_LEVEL_OTHERS);
		
		// read current output of pin
		_checker.get_pin_value(current_pin_value);
		
		// apply select
		select.write(status, tmr_out_select);
		#0.1us;
		
		if (_checker.is_jtag_tdo_pin() == 1'b0) begin
			// check no change
			_checker.check_pin_value(current_pin_value);
		end
		
		// apply enable
		enable.write(status, 1'b1);
		
		// check output of signal
		_checker.check_selected();
		
		if (_checker.is_jtag_pin == 1'b1) begin
			initialize_again();
		end
		else begin
			// reverse enable
			enable.write(status, 1'b0);
			#0.1us;
		end
		
		if (_checker.is_jtag_tdo_pin() == 1'b0) begin
			// check for original value
			_checker.check_pin_value(current_pin_value);
		end
		
		enable.write(status, 1'b0);
		select.write(status, 0);
		if (_checker.is_jtag_pin) begin
			jtag_enable_tdo_output();
		end
		#5us;
	endtask
endclass
