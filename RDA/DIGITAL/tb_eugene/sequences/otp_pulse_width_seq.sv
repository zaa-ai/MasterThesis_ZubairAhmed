class otp_pulse_width_seq extends base_dsi_master_seq;
	
	string PATH_OTP_CK;
		
    `uvm_object_utils(otp_pulse_width_seq)

    function new(string name = "");
        super.new("otp_pulse_width");
    endfunction : new

    jtag_tr jtag_trans;
    
    virtual task run_tests();
		PATH_OTP_CK = { `STRING_OF(`OTP_INST) , ".CK"};
		log_sim_description("Testcase for OTP pulse width setting", LOG_LEVEL_TOP);
    	
        #100us;
        //clear interrupts
        regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.write(status, 16'hFFFF);
        #100us;
        
        jtag_enable_with_tdo();
		measure_clock_frequency(18_000_000, 0_500_000);
        check_write_pulse_length("f__OSC,OSC20M__=18MHz");
        
		trim_oscillator_to_22MHz();
		measure_clock_frequency(22_000_000, 0_500_000);
        
        test_regmodel.TEST_OTP_CONFIG.OTP_test_registers.OTP_WRITE_PULSE_WIDTH.PULSE_WIDTH.write(status, 2208);
        log_sim_check(test_regmodel.TEST_OTP_CONFIG.OTP_test_registers.OTP_WRITE_PULSE_WIDTH.get_name(), , "PASS");
        check_write_pulse_length("f__OSC,OSC20M__=22MHz");
        
        jtag_disable();
        #100us;
    endtask
	
	virtual task trim_oscillator_to_22MHz();
		jtag_write_elip_seq elip_write_seq;
		`uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == ADDR_TIMEBASE_TRIM_OSC; data == 32'h0000_0067; init == 1'b0;})
		#200us;
	endtask
	
	virtual task measure_clock_frequency(int expected_frequncy, int tolerance);
		time first, second, period, expected_period;
		
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.EN_RFC.set(1);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.SEL_RFC.set(20);
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.update(status);
		
		#5us;
		@(posedge rfc.D);
		first = $time();
		@(posedge rfc.D);
		second = $time();
		period = second - first;
		expected_period = 1s/expected_frequncy;
		
		compare_times(period, expected_period, "clock period is not set correctly", ((1s/(expected_frequncy-tolerance))-expected_period));
		log_sim_measure("f__OSC,OSC20M__", $sformatf("%5.2f",1.0us/period), $sformatf("oscillator frequency @ %5.2fMHz", expected_frequncy/1000000.0));
		
		#5us;
		test_regmodel.TEST_TOP.TEST_TOP.TMR_OUT_RFC.write(status, 0);
		#5us;
	endtask
    
    virtual task check_write_pulse_length(string condition);
        logic [11:0] addr[$];
        logic [11:0] data[$];
        int start_addr=0;
        
        log_sim_description($sformatf("OTP program pulse width with %s", condition), LOG_LEVEL_SEQUENCE);
        
        // switch system clock to CLK
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.CLKSW_TST_EN.set(1);
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.CLKSW_TST_SEL.set(0);
		test_regmodel.TEST_OSC.TEST_OSC.TMR_DIG_TB.update(status);
        
        // OTP BIST Control Register
        // set EN_SOAK, OTP_WRITE
		test_regmodel.TEST_OTP.Test_Registers.OTP_BIST_CONTROL.write(status, '0);
		test_regmodel.TEST_OTP.Test_Registers.OTP_BIST_CONTROL.EN_SOAK.set(1);
		test_regmodel.TEST_OTP.Test_Registers.OTP_BIST_CONTROL.OTP_READ.set(1);
		test_regmodel.TEST_OTP.Test_Registers.OTP_BIST_CONTROL.update(status);

        repeat(2) begin
            prog($urandom_range(4095,0), $urandom_range(4095,0), condition);
		end
        repeat(2) begin
            prog($urandom_range(4095,0), $urandom_range(4095,0), condition);
		end
        
        start_addr = $urandom_range(4075,0); // start_addr < 4095 - array length
        
        for (int i=0 ; i< 20 ; i++) begin
            addr.push_back(12'(start_addr+i));
            data.push_back($urandom_range(4095,0));
            
            prog(addr[i], data[i], condition);
        end
        
        // set VRR1 : MRR[3] = 1
		test_regmodel.TEST_OTP.Test_Registers.OTP_CONFIG.OTP_MRR.write(status, 4);
        // set SEL_MRR
		test_regmodel.TEST_OTP.Test_Registers.OTP_BIST_CONTROL.SEL_MRR.write(status, 1);

        // check array
        for (int i=0; i < 20; i++) begin
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == OTP_READ;
        			dr_value == 266'({addr[i],20'h00000});  dr_length == 32; init_jtag == 1'b0;})
            // data would shifted out in the second JTAG transaction
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == OTP_READ;
        			dr_value == 266'({addr[i],20'h00000});  dr_length == 32; init_jtag == 1'b0;})
            
            `uvm_info(get_type_name(), $sformatf("reading %3h @ %3h",jtag_trans.read_dr[11:0], addr[i]), UVM_MEDIUM)
            
            if (jtag_trans.read_dr[11:0] !== data[i]) begin
               `uvm_error(get_type_name(), $sformatf("Write OTP BIST with SOAK, Data @ adress %h is expected %h but is %h",addr[i],data[i],jtag_trans.read_dr[11:0]))
            end             
            #250ns;
        end 
    endtask
    
    task prog(input int address, input int data, string condition="");
        bit ready = 1'b0;
        // write
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == OTP_WRITE;
        		dr_value == 266'({address[11:0], data[11:0]});    dr_length == 24; init_jtag == 1'b0;})
       fork
		   repeat (4)
			   measure_CK_pulses(condition);
	   join_none
        while (~ready) begin
            #100us;
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == OTP_BIST_STAT;
                    dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})
            if (jtag_trans.read_dr[7] == 1'b1 && jtag_trans.read_dr[12] == 1'b0) begin
                ready = 1'b1;
            end
        end     
	endtask
	
	task measure_CK_pulses(string condition);
		time ck_posedge, ck_negedge, pulse_width;
		wait_for_CK_equals(1'b0);
		wait_for_CK_equals(1'b1);
		ck_posedge = $time() - 100ns;
		wait_for_CK_equals(1'b0);
		ck_negedge = $time() - 100ns;
		pulse_width = ck_negedge - ck_posedge;
		if (pulse_width > 1us) begin
			compare_times(pulse_width, 101us, "CK pulse is not correct", 1us);
			log_sim_measure("t__OTP,prog_pulse__", $sformatf("%7.2f",(pulse_width)/1.0us), condition, "");
		end
	endtask
	
	task wait_for_CK_equals(logic value);
		uvm_hdl_data_t	ck_level;
		do begin 
			ck_level = hdl_read(PATH_OTP_CK);
			#100ns;
		end while (ck_level[0] != value);
	endtask
endclass
