class base_dsi_master_seq extends top_default_seq;
	
	`uvm_object_utils(base_dsi_master_seq)
	
	dsi3_transaction_recorder transaction_recorder;
	edf_parameter_model edf_parameters;
	
	virtual OTP_model_if OTP_model; 
	virtual sequence_if sequence_if_inst;
	virtual clk_osc_if clk_osc_if_inst;
    string  previous_sequence;
	
	simulation_logger logger;
	bit log_task_name = 1'b1;
	register_util registers;
	
	function new(string name = "");
		super.new(name);
		logger = new("sim_logger");
		registers = new("registers", logger);
	endfunction : new
		
	`define ds_agent_func(_name_) \
		task set_``_name_ (logic in); \
			digital_signal_tr _ds_tr; \
			digital_signal_t _in = _ds_tr.convert2enum(in); \
			`uvm_do_on_with(_ds_tr, m_``_name_``_agent.m_sequencer, {_val==local::_in;}) \
		endtask : set_``_name_ \
		\
		function logic get_``_name_ (); \
			return m_``_name_``_agent.m_config.vif.D; \
		endfunction : get_``_name_ \
		\
		virtual function void check_``_name_ (logic expected_value); \
			logic	_name_ = get_``_name_``(); \
			if (_name_ !== expected_value) begin \
				`uvm_error(this.get_type_name(), $sformatf("``_name_ is not set correctly. Got %1b, but expected %1b", _name_, expected_value)) \
			end \
		endfunction
	
		
	`define real_agent_func(_name_) \
		task set_``_name_(real voltage, time set_time=1us); \
			longint vol, dur; \
			real_signal_tr rs_tr; \
			vol = longint'(voltage / m_``_name_``_agent.m_config.value_scale); \
			dur = longint'(set_time / m_``_name_``_agent.m_config.time_scale); \
			`uvm_do_on_with(rs_tr, m_``_name_``_agent.m_sequencer, {value==local::vol; duration==local::dur; edge_duration==local::dur;}) \
		endtask : set_``_name_ \
		\
		function real get_``_name_ (); \
			return m_``_name_``_agent.m_config.vif.PIN; \
		endfunction : get_``_name_
	
	
	/************************ SPI Command Macros ************************/
	`include "spi_frame_macros.sv"
	
	`ds_agent_func (tmode)
	`ds_agent_func (resb)
	`ds_agent_func (rfc)
	`ds_agent_func (bfwb)
	`ds_agent_func (dab)
	`ds_agent_func (intb)
	`ds_agent_func (syncb)
	`ds_agent_func (syncb_out)
	
	`real_agent_func(vsup)
	`real_agent_func(vcc)
	`real_agent_func(vdd18)
	`real_agent_func(aout)
	`real_agent_func(ldo)
	`real_agent_func(temp)
	
	virtual task body();

		if (!uvm_config_db #(dsi3_transaction_recorder)::get(null, "", "dsi3_transaction_recorder", transaction_recorder)) begin
			`uvm_error(get_type_name(), "Failed to get DSI transaction recorder from uvm_config_db!")
		end
		if (!uvm_config_db #(edf_parameter_model)::get(null, "", "edf_parameter_model", edf_parameters)) begin
			`uvm_error(get_type_name(), "Failed to get edf_parameter_model from uvm_config_db!")
		end
		if (!uvm_config_db#(virtual OTP_model_if)::get(m_sequencer, "", "OTP_model_if_inst", OTP_model)) begin
			`uvm_error(get_type_name(), "Unable to get OTP model interface from config DB!")
		end
		if (!uvm_config_db#(virtual sequence_if)::get(m_sequencer, "", "sequence_if_inst", sequence_if_inst)) begin
			`uvm_error(get_type_name(), "Unable to get sequence_if interface from config DB!")
		end
		if (!uvm_config_db#(virtual clk_osc_if)::get(m_sequencer, "", "clk_osc_if_inst", clk_osc_if_inst)) begin
			`uvm_error(get_type_name(), "Unable to get clk_osc_if interface from config DB!")
		end
		`uvm_info(get_type_name(), $sformatf("%s sequence starting", this.get_type_name()), UVM_MEDIUM)
		
        set_sequence_interface(get_name());
		
		#1ns;
		set_tmode(1'b0);
		
		// perform power up only if this is a 'standalone' top sequence
		if(m_parent_sequence == null) begin
			if(log_task_name == 1'b1) begin
				log_sim_task(this.get_name());
			end
			power_up();
			#500us;
		end
		
		run_tests();
				
		if(m_parent_sequence == null) begin		
			#100us;
			log_sim_status("PASS");
			log_sim_end($sformatf("%s sequence completed", this.get_name()));
        end
        
        reset_sequence_interface();
        
	endtask
    
    virtual function void set_sequence_interface(string new_sequence);
        sequence_if_inst.sequence_count = sequence_if_inst.sequence_count + 1;
        previous_sequence = sequence_if_inst.current_sequence;
        sequence_if_inst.current_sequence = new_sequence;
    endfunction
    
    virtual function void reset_sequence_interface();
        sequence_if_inst.sequence_count = sequence_if_inst.sequence_count + 1;
        sequence_if_inst.current_sequence = previous_sequence;
    endfunction
    
	/**
	 * Must be overridden by sub classes to execute all tests.
	 */
	virtual task run_tests();
		`uvm_error(this.get_type_name(), "task 'run_tests' has to be overridden by sub classes");
	endtask
	
	virtual function void log_sim_task(string task_name, string description = "");
		logger.log_sim_task(task_name, description); 
	endfunction
	
	virtual function void log_sim_description(string description, int level = 0);
		logger.log_sim_description(description, level);
	endfunction
	
	virtual function void log_sim_measure (string parameter_name, string value, string condition = "", string status = "");
		logger.log_sim_measure (parameter_name, value ,condition , status);
	endfunction
	
	virtual function void log_sim_check (string element_name, string condition = "", string status = "");
		logger.log_sim_check (element_name, condition , status);
	endfunction
	
	virtual function void log_sim_status (string status );
		logger.log_sim_status(status);
	endfunction
	
	virtual function void log_sim_end (string text = "");
		logger.log_sim_end (text);
	endfunction
	
	virtual task power_up (time waiting=1500us);
		osc_tr osc;
		
		set_vsup(12, 20us);
		#100us;
		set_resb(1'b1);
		set_syncb(1'b0);
		`uvm_do_on_with (osc, m_osc_agent.m_sequencer, {enabled == 1; freq==500000;})

		#(waiting);
	endtask : power_up
	
	virtual task power_down (time waiting=500us);
		set_vsup(0, 20us);
		#(waiting);
	endtask : power_down	
	
	virtual task reset(string otp_file_name="", time rfc_timeout = 5ms);
		
		if(otp_file_name != "") begin
			read_otp(otp_file_name);
		end
		
		`ifdef GATE_LEVEL
			set_clock_ref(.enable(1'b0));
			#10us;
		`endif
		
		set_resb(0);
		`ifdef GATE_LEVEL
			#10us;
			set_clock_ref(.enable(1'b1));
		`endif
		#100us;
		set_resb(1); 
		wait_for_rfc(rfc_timeout);
	endtask
	
	virtual task wait_for_rfc(time timeout = 5ms);
		fork
			begin
				@(posedge rfc.D);
			end 
			begin
				#timeout;
				`uvm_error(this.get_type_name(), $sformatf("there was no RFC after 5ms, something is wrong here"))
			end	
		join_any
		disable fork;
	endtask
	
	// wait for DAB or 500us timeout
	virtual task wait_for_dab(time timeout = 500us, bit error_after_timeout = 1'b0);
		fork
			begin
				@(negedge dab.D);
			end 
			begin
				#(timeout);
				if(error_after_timeout == 1'b1) begin
					`uvm_error(this.get_type_name(), $sformatf("there was no DAB after expected timeout of %0fus", timeout/1.0us))
				end
			end	
		join_any
		disable fork;
	endtask
	
	virtual task wait_for_voltage_edge_at_channel(int channel, time timeout = 100us);
		dsi3_master_agent dsi_master_agent;
		dsi_master_agent = get_master_agent(channel);
		fork
			begin
				@(dsi_master_agent.m_config.vif.cable.Voltage);
			end 
			begin
				#(timeout);
				`uvm_error(this.get_type_name(), $sformatf("there was no voltage edge at channel %0d after expected timeout of %0fus", channel, timeout/1.0us))
			end	
		join_any
		disable fork;
	endtask
	
	virtual task set_clk_ref(int frequency);
		osc_tr osc;
		`uvm_do_on_with (osc, m_osc_agent.m_sequencer, {enabled == (frequency > 0); freq==frequency;})
	endtask
	
	task set_vdd1v8_force(real value);
		string real_string =  $sformatf("%.2f", value);
		$hdl_xmr_force("top_tb.th.i_dut_wrapper.i_dut.xtop.XANA.VDD18",real_string, ,"freeze", );
	endtask : set_vdd1v8_force
			
	task set_vdd1v8_release ();
		$hdl_xmr_release("top_tb.th.i_dut_wrapper.i_dut.xtop.XANA.VDD18");
	endtask : set_vdd1v8_release
	
	virtual function void check_value_at_path(string path, int expected_value);
		uvm_hdl_data_t value;
		value = hdl_read(path);
		if (value[31:0] != expected_value) `uvm_error(this.get_type_name(), $sformatf("unexpected value at path '%s', expected 0x%0h but got 0x%0h", path, expected_value, value[31:0]))
	endfunction
	
	virtual task jtag_enable_with_tdo(bit initialize_jtag = 1'b0);
		jtag_enable(initialize_jtag);
		jtag_enable_tdo_output();
	endtask
	
	virtual task jtag_enable(bit initialize_jtag = 1'b0);
		`uvm_info("JTAG", "JTAG ENABLE", UVM_HIGH)
		hdl_force("top_tb.th.i_dut_wrapper.xtop.DAB_P", 1'b0);
		hdl_force("top_tb.th.i_dut_wrapper.xtop.BFWB_P", 1'b0);
		#1us;	
		set_tmode(1'b1);
		#1us;
		hdl_release("top_tb.th.i_dut_wrapper.xtop.DAB_P");
		hdl_release("top_tb.th.i_dut_wrapper.xtop.BFWB_P");
		#1us;
		if (initialize_jtag == 1'b1) begin
			jtag_tr t;
			`uvm_do_on_with(t, m_jtag_master_agent.m_sequencer, {ir_length == 0; dr_length == 0; init_jtag == 1;})
			#1us;
		end
	endtask : jtag_enable
	
	virtual task jtag_enable_tdo_output();
		test_regmodel.TEST_TOP.TEST_TOP.TMR_DIG.USE_JTAG.write(status, 1'b1);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.EN_DAB.set(1'b0);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.SEL_DAB.set(0);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.EN_INTB.set(1'b1);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.SEL_INTB.set(2);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_DAB_INTB.update(status);
		#1us;
	endtask
	
	virtual task jtag_disable();
		`uvm_info("JTAG", "JTAG DISABLE", UVM_HIGH)
		set_tmode(1'b0);
		#2us;
	endtask : jtag_disable
    
	virtual task enable_ecps_pattern();
		jtag_enable();
		hdl_force("top_tb.th.i_dut_wrapper.enable_pattern", 1'b1);
	endtask
	
	virtual task disable_ecps_pattern();
		hdl_force("top_tb.th.i_dut_wrapper.enable_pattern", 1'b0);
		jtag_disable();
	endtask
	
	task read_otp (string file_name);
		OTP_model.dat_file = file_name;
		`uvm_info(this.get_type_name(), $sformatf("changed OTP content using file: %s", file_name), UVM_MEDIUM)
	endtask
	
	virtual task set_clock_ref(int freq = 500000, bit enable = 1'b1);
		osc_tr osc;
		`uvm_do_on_with (osc, m_osc_agent.m_sequencer, {enabled == local::enable; freq == local::freq;})
	endtask		
	
	virtual task set_clock_en_hw(bit value);
		m_config.m_osc_config.vif.EN = value;
	endtask
	
	task disable_dsi_channels(logic[project_pkg::DSI_CHANNELS-1:0] channels);
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, project_pkg::DSI_CHANNELS'(~channels));
	endtask
	
	task enable_dsi_channels(logic[project_pkg::DSI_CHANNELS-1:0] channels);
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, project_pkg::DSI_CHANNELS'(channels));
	endtask
    
	virtual task clear_all_irqs();
		regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.write(status, 16'hFFFF);
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hFFFF);
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.write(status, 16'hFFFF);
		regmodel.Supply.supply_registers.SUP_IRQ_STAT.write(status, 16'hFFFF);
		regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.write(status, 16'hFFFF);
		regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.write(status, 16'hFFFF);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.write(status, 16'hFFFF);
		end
	endtask
	
	virtual task check_ic_revision();
		uvm_reg_data_t value;
		regmodel.Info.IC_revision_and_ID_registers.IC_REVISION.read(status, value);
		if(value < 1000 || value > 1800) begin
			`uvm_error(this.get_type_name(), $sformatf("register read of IC_REVISION got unexpected value of %0d", value));
		end
		log_sim_measure("IC_REV", $sformatf("%0d",value), "", "Tape out revision");
	endtask
	
	virtual function void compare_times(time time1, time time2, string message, time delta=0.0us);
		time diff = (time1 > time2) ? time1-time2 : time2-time1;
		if(diff > delta) begin
			`uvm_error(this.get_name(), $sformatf("%s differ by %0fus, expected maximum difference is %0fus.", message, diff/1.0us, delta/1.0us )) 
		end
	endfunction
	
	virtual task set_dsi_uv(project_pkg::dsi_logic_t channels='0);
		for (int ch=0; ch < project_pkg::DSI_CHANNELS; ch++) begin
			set_dsi_uv_for_channel(ch, channels[ch]);
		end
	endtask
	
	virtual task set_dsi_ov(project_pkg::dsi_logic_t channels='0);
		for (int ch=0; ch < project_pkg::DSI_CHANNELS; ch++) begin
			set_dsi_ov_for_channel(ch, channels[ch]);
		end
	endtask

	virtual task set_dsi_uv_for_channel(int channel, bit value);
		string path;
		path = $sformatf("%s[%0d]", PATH_DSI3_UVB, channel);
		force_or_release_path(value, path, ~value);
	endtask
    
	virtual task set_dsi_ov_for_channel(int channel, bit value);
		string path;
		path = $sformatf("%s[%0d]", PATH_DSI3_OV, channel);
		force_or_release_path(value, path, value);
	endtask
    
	virtual task set_vcc_uv(bit value);
		force_or_release_path(value, PATH_VCC_OK, 0);
	endtask
	
	virtual task set_cldo_uv(bit value);
		force_or_release_path(value, PATH_LDO_OK, 0);
	endtask
	
	virtual task set_ref_fail(bit value);
		force_or_release_path(value, PATH_VRR_OK, 0);
    endtask
    
    task set_iload(real load, int channel, time set_time=1us);
        longint vol, dur;
        real_signal_tr  load_seq;
        vol = longint'(load / m_iload_agent[channel].m_config.value_scale);
        dur = longint'(set_time / m_iload_agent[channel].m_config.time_scale);
        `uvm_do_on_with(load_seq, m_iload_agent[channel].m_sequencer, {value==local::vol; duration==local::dur; edge_duration==local::dur;})
    endtask
	
	virtual task force_or_release_path(bit option, string path, int value=0);
		if (option) begin
			if (!uvm_hdl_force(path, value))
				`uvm_error(this.get_type_name(), $sformatf("could not force %s to %1d", path, value))
			else
				`uvm_info(this.get_type_name(), $sformatf("forced %s to %1d", path, value), UVM_HIGH)
		end 
		else begin
			if (!uvm_hdl_release(path))
				`uvm_error(this.get_type_name(), $sformatf("could not release %s", path))
			else
				`uvm_info(this.get_type_name(), $sformatf("released %s", path), UVM_HIGH)
		end
	endtask
	
	virtual function void check_dsi_voltages(project_pkg::dsi_logic_t	expected_voltages);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			logic	current_voltage;
			current_voltage = get_dsi_voltage(channel);
			if (current_voltage != expected_voltages[channel]) begin
				`uvm_error(this.get_type_name(), $sformatf("Voltage of DSI channel %1d is not as expected! Exp. %1b but got %1b", channel, expected_voltages[channel], current_voltage))
			end
		end
	endfunction
	
	virtual function void check_dsi_voltages_for_all_channels(logic	expected_voltage);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			logic	current_voltage;
			current_voltage = get_dsi_voltage(channel);
			if (current_voltage != expected_voltage) begin
				`uvm_error(this.get_type_name(), $sformatf("unexpected voltage at DSI channel %0d, expected:%1b, got: %1b", channel, expected_voltage, current_voltage))
			end
		end
	endfunction
	
	virtual function logic get_dsi_voltage(int channel);
		dsi3_master_agent dsi_master_agent;
		dsi_master_agent = get_master_agent(channel);
		return dsi_master_agent.m_config.vif.cable.Voltage;
	endfunction

	/**
	 * Sets a new TDMA scheme to be used for random CRM slave answers.
	 */
	function void set_tdma_scheme_crm(int channel, tdma_scheme scheme);
		get_slave_agent(channel).m_config.crm_scheme = scheme;
	endfunction
	
	/**
	 * Sets a new TDMA scheme to be used for random PDCM slave answers.
	 */
	function void set_tdma_scheme_pdcm(int channel, tdma_scheme scheme);
		get_slave_agent(channel).m_config.pdcm_scheme = scheme;
	endfunction
	
	/**
	 * Sets a new TDMA scheme to be used for random DM slave answers.
	 */
	function void set_tdma_scheme_dm(int channel, tdma_scheme scheme);
		get_slave_agent(channel).m_config.dm_scheme = scheme;
	endfunction
	
	/**
	 * Adds a new TDMA scheme to the selected DSI Slave transmission FIFO.  
	 */
	function void add_slave_crm_scheme(int channel, tdma_scheme scheme);
		get_slave_agent(channel).m_crm_tdma_scheme_port.write(scheme);
	endfunction
	
	function void add_slave_pdcm_scheme(int channel, tdma_scheme scheme);
		get_slave_agent(channel).m_pdcm_tdma_scheme_port.write(scheme);
	endfunction

	/**
	 * Clear TDMA scheme FIFOs.  
	 */
	function void clear_slave_crm_scheme_fifos();
		for (int ch=0; ch < project_pkg::DSI_CHANNELS; ch++) begin
			clear_slave_crm_scheme_fifo(ch);
		end
	endfunction
	
	function void clear_slave_crm_scheme_fifo(int channel);
		get_slave_agent(channel).m_master_subscriber.crm_tdma_fifo.flush();
	endfunction
	
	function void clear_slave_pdcm_scheme_fifos();
		for (int ch=0; ch < project_pkg::DSI_CHANNELS; ch++) begin
			clear_slave_pdcm_scheme_fifo(ch);
		end
	endfunction
	
	function void clear_slave_pdcm_scheme_fifo(int channel);
		get_slave_agent(channel).m_master_subscriber.pdcm_tdma_fifo.flush();
	endfunction
	
	function dsi3_slave_agent get_slave_agent(int channel);
		if(channel < project_pkg::DSI_CHANNELS) begin
			return m_dsi3_slave_agent[channel];
		end
		`uvm_fatal(this.get_type_name(), $sformatf("no slave agent exists for channel index: %d", channel))
	endfunction
	
	function dsi3_master_agent get_master_agent(int channel);
		if(channel < project_pkg::DSI_CHANNELS) begin
			return m_dsi3_master_agent[channel];
		end
		`uvm_fatal(this.get_type_name(), $sformatf("no master agent exists for channel index: %d", channel))
	endfunction
	
	function dsi3_slave_config get_dsi3_slave_config(int channel);
		dsi3_slave_agent agent = get_slave_agent(channel);
		return	agent.m_config;
	endfunction
	
	function dsi3_master_config get_dsi3_master_config(int channel);
		dsi3_master_agent agent = get_master_agent(channel);
		return	agent.m_config;
	endfunction
	
	function checker_config get_checker_config();
		return checker_config::get();
	endfunction
	
	/**
	 * Checks DSI_CMD.CMD register (currently executed command).
	 */
	task check_DSI_CMD(spi_cmd_type expected_cmd_type);
		foreach (regmodel.DSI[channel]) begin
			registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_CMD.CMD, 64'(expected_cmd_type), .measure_register(1'b1));
		end
	endtask
	
	`include "dsi3_packet_utilities.svh"
	
	/*
	 * Pattern stuff
	 */
	
	/*
	 * Enable ECPS pattern functionality
	 */
	virtual task pattern_enable();
		hdl_force("top_tb.th.i_dut_wrapper.enable_pattern", 1'b1);
  	  	#10us;
	endtask
	
	/*
	 * Disable ECPS pattern functionality
	 */
	virtual task pattern_disable();
		hdl_force("top_tb.th.i_dut_wrapper.enable_pattern", 1'b0);
  	  	#10us;
	endtask
	
	/*
	 * Gets ECPS generated pattern wrapper.  
	 */
	virtual function M52144A_pattern_wrapper get_pattern_wrapper();
		M52144A_pattern_wrapper wrapper;
  	  	if (!uvm_config_db#(M52144A_pattern_wrapper)::get(m_sequencer, "", "pattern_wrapper", wrapper)) begin 
  			`uvm_error(get_type_name(), "Unable to get pattern wrapper from config DB!")
	  	end
  	  	return wrapper;
	endfunction
	
	virtual function void hdl_force(string path, uvm_hdl_data_t value);
		if (! uvm_hdl_force(path, value)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
	endfunction
	
	virtual function void hdl_release(string path);
		if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
	endfunction
	
	virtual function uvm_hdl_data_t hdl_read(string path);
		uvm_hdl_data_t	_value;
		if (! uvm_hdl_read(path, _value)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
		return _value;
    endfunction
    
    /**
     * Flip one or two bits in Word stored at given SRAM address 
     */
    virtual task flipp_bits_in_sram(input logic [11:0] ram_address, input error_t bit_error);
        /**
         * RAM: 3072 words with 16 words per row and a total number of 192 rows
         * row_addr = ram_addr >> 4;
         * mux_addr = ram_addr & 0xF;
         * bits of word in row -> every mux_addr + i*16 position
         * eg.
         * ram_addr = 0x28 -> row_addr = 0x28 >> 4 = 2
         *             -> mux_addr = 0x28 & 0xF = 8
         *             => data bits in row at bits 8, 24, 40 etc.
         */
        int first_bit_position;
        int second_bit_position;
        int row_addr;
        int mux_addr;
        int first_bit_in_row;
        int second_bit_in_row;
        uvm_hdl_data_t flipped_bit;
        string ram_path = PATH_SRAM_MEM_ROW;
        
        row_addr = ({20'd0, ram_address} - {16'd0,project_pkg::BASE_ADDR_RAM}) >> 4;
        mux_addr = ({20'd0, ram_address} - {16'd0,project_pkg::BASE_ADDR_RAM}) & 32'hF;
        std::randomize(first_bit_position) with {first_bit_position >= 0; first_bit_position<16;};
        std::randomize(second_bit_position) with {second_bit_position >= 0; second_bit_position<16; second_bit_position != first_bit_position;};
        first_bit_in_row = mux_addr + (first_bit_position * 16);
        second_bit_in_row = mux_addr + (second_bit_position * 16);
        
        if (!uvm_hdl_read($sformatf(ram_path,row_addr),flipped_bit)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", $sformatf(ram_path,row_addr)))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %0h", $sformatf(ram_path,row_addr), flipped_bit[367:0]), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("read word = %0h", extractWordFromRamRow(flipped_bit[367:0],mux_addr)), UVM_INFO)
        flipped_bit[first_bit_in_row] = ~flipped_bit[first_bit_in_row];
        if(bit_error == TWO_BIT_ERR) begin
            flipped_bit[second_bit_in_row] = ~flipped_bit[second_bit_in_row];
        end
        `uvm_info(this.get_type_name(), $sformatf("force %s with %0h", $sformatf(ram_path,row_addr), flipped_bit[367:0]), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("flipped word = %0h", extractWordFromRamRow(flipped_bit[367:0],mux_addr)), UVM_INFO)
        if( !uvm_hdl_deposit($sformatf(ram_path,row_addr), flipped_bit)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed", $sformatf(ram_path,row_addr)))
    endtask
    
    virtual function logic[15:0] extractWordFromRamRow(logic[367:0] rowData, int muxAddr);
        logic[15:0] data = '0;
        for (int i = 0; i < 16; i++) begin
            data[i] = rowData[muxAddr + i*16];
        end
        return data;
    endfunction
	
endclass : base_dsi_master_seq

`include "seq_list.svh"

