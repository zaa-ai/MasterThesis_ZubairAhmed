class otp_test_seq extends base_dsi_master_seq;

	`uvm_object_utils(otp_test_seq)

	function new(string name = "");
		super.new("otp_test");
	endfunction : new
    //BASE_ADDR_OTP
    jtag_write_elip_seq            elip_write_seq;
    jtag_tr jtag_trans;
    
    const int c_otp_array_size = 4096;
    
	virtual task run_tests();
        string file_otp;
		
		log_sim_description("Testcase for OTP production test", LOG_LEVEL_TOP);
        
        file_otp = $sformatf("otp_unprogrammed.dat");
        read_otp(file_otp);

        set_resb(0);
        #100us;
        set_resb(1);    
        #1ms;
        otp_direct_access ();
        #1ms;
        otp_sense_amplifier_p();
        #1ms;
        otp_sense_amplifier_n();
        #1ms;
        word_line_continuity_test ();
        #1ms;
        bit_line_continuity_test();
        #1ms;
        program_cell_stress_test();
        #1ms;
        read_cell_stress_test();
        #1ms;
        array_clean_test();
        #1ms;
	endtask
    
    task otp_direct_access ();
        log_sim_description("Testing direct access to OTP via OTP_CFG", LOG_LEVEL_SEQUENCE);
        /*
	     * Für JIRA-NOTE internal: (P17402-218)
	     * */
        //TMODE high
        jtag_enable_with_tdo();

        //alle bits im OTP_CFG register klappern lassen
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha0;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b1;})       
        for (int i=1; i<'h8000; i=i*2) begin
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha0;
        			dr_value == 266'(i);  dr_length == 16; init_jtag == 1'b0;})   
        end
        //reset OTP_CFG
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha0;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        
        // TMODE low
        jtag_disable();
        `uvm_info(get_type_name(), "end task: otp_direct_access", UVM_MEDIUM)       
	endtask
	
    /**
     * according to Document "Test / PGM OTP via jtag"
     * 
     * http://svnhost.elmos.de/department/ds/ds_download/download20140409/HDL/STD_Memory/OTP_WRAPPER_TSMC_24MHZ/release/1.50/OTP_WRAPPER_TSMC_24MHZ/doc/otp_test_low_level_eldo.pdf
     * 
     * Attention:
     * 
     * Before setting tRP (for configure read pulse length) measure the the oscillator frequency (because it is not trimmed).
     * Calculate the value for tRP whith the measured frequency.
     * 
     * */
    
    /*### 1.1  Sense Amplifier Test Mode P   ######################################################
     * 
     * This test is for Single-Ended read mode (compare memory cell to a reference). To ensure Sense
     * Amplifier output not stuck at 0.
     * Perform a single-ended read at any address with MR[3]=1 (SA Test Mode P). This sets the input
     * of the sense amplifier to VREF instead of the normal bit lines. Use MR[6]=0, so that VREF is
     * internally pulled to VDD and the sense amplifier output reads as 1 regardless of the memory
     * content.otp_conf
     * Address: Any address location, programmed or un-programmed.
     * Voltage: Nominal VDD voltage supply level.
     * 
     * */
    task otp_sense_amplifier_p ();
		log_sim_description("1.1  Sense Amplifier Test Mode P", LOG_LEVEL_SEQUENCE); 
        //TMODE high
        jtag_enable_with_tdo();

        // switch system clock to CLK       
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'hb2;
                dr_value == 266'h0;  dr_length == 0; init_jtag == 1'b0;})
        // Sel SA Test Mode P: MR[3]=1
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h0800_0000;  dr_length == 32; init_jtag == 1'b0;})   
        // Set TRP[6:0] in OTP Read Config Register to decimal 5, should give a read time of 220ns...
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha7;
                dr_value == 266'h0003_0000;  dr_length == 32; init_jtag == 1'b0;})   
        // Set SEL_MR and SEL_RD in OTP BITS Control Register
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0440;   dr_length == 16; init_jtag == 1'b0;})
        // read data from OTP 12 bit data, 12 bit adr
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'haaa000; dr_length == 24; init_jtag == 1'b0;})       
        //wait for 250ns;
        #250ns;
            // read data from OTP expect 0xffffff on TDO...
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'haaa000; dr_length == 24; init_jtag == 1'b0;})
        if (jtag_trans.read_dr !== 266'hfff) begin
            `uvm_error(this.get_type_name(), $sformatf("otp sense ampliefier test mode P: TDO is not as expected, expected 0xfff but is %h", jtag_trans.read_dr))   ;           
        end 
        // reset MR 
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h0000000000; dr_length == 40; init_jtag == 1'b0;})       
        // reset SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0000000000; dr_length == 40; init_jtag == 1'b0;})       
        // Switch off alternate function of MISO2 to TDO
        `uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == 'h0080; data == 'h0003; init == 1;}) // enable SPI1 and SPI2
        `uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == 'h0082; data == 'h0000; init == 1;}) // disable MISO2 as TDO
		#2us;
        // TMODE low
        jtag_disable();
        `uvm_info(get_type_name(), "end task: otp_sense_amplifier_p", UVM_MEDIUM)
    endtask : otp_sense_amplifier_p
    
    /*### 1.2 Sense Amplifier Test Mode N   ######################################################
     * 
     * This test is for Single-Ended read mode (compare memory cell to a reference). To ensure Sense
     * Amplifier output not stuck at 1.
     * Perform a single-ended read at any address with MR[5]=1 (SA Test Mode N). This adds VREF
     * voltage to the reference side of the sense amplifiers. Use MR[6]=0, so that VREF is internally
     * pulled to VDD and the sense amplifier output reads as 0 regardless of the memory content.
     * Address: Any address location, preferably un-programmed.
     * Voltage: Nominal VDD voltage supply level.
     * 
     * 
     * */
    task otp_sense_amplifier_n ();

		log_sim_description("1.2 Sense Amplifier Test Mode N", LOG_LEVEL_SEQUENCE);
        //TMODE high
        jtag_enable_with_tdo();
        // switch system clock to CLK       
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'hb2;
                dr_value == 266'h0;  dr_length == 0; init_jtag == 1'b0;})
        // Sel SA Test Mode N: MR[5]=1
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h2000_0000;  dr_length == 32; init_jtag == 1'b0;})
        // Set TRP[6:0] in OTP Read Config Register to decimal 5, should give a read time of 220ns...
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha7;
                dr_value == 266'h0003_0000;  dr_length == 32; init_jtag == 1'b0;})   
        // Set SEL_MR and SEL_RD in OTP BITS Control Register
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0440;   dr_length == 16; init_jtag == 1'b0;})
        // read data from OTP 12 bit data, 12 bit adr
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'haaa000; dr_length == 24; init_jtag == 1'b0;})       
        //wait for 250ns;
        #250ns;
            // read data from OTP expect 0xffffff on TDO...
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'haaa000; dr_length == 24; init_jtag == 1'b0;})
        if (jtag_trans.read_dr !== 266'h000) begin
            `uvm_error(this.get_type_name(), $sformatf("sense amplifier test mode N: TDO is not as expected, expected 0x000 but is %h", jtag_trans.read_dr))    ;           
        end 
        // reset MR 
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h0000_0000;  dr_length == 32; init_jtag == 1'b0;})       
        // reset SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        
		#2us;
		// TMODE low
        jtag_disable();
        `uvm_info(get_type_name(), "end task: otp_sense_amplifier_n", UVM_MEDIUM)
    endtask : otp_sense_amplifier_n
    
    /*### 1.3  Word-line continuity test   ######################################################
     * 
     * To ensure continuity of all word-lines and confirm address decoding.
     * Set MR[1]=1 couples a programmed ROM bit-line with the last column in the array. A singleended
     * read results in a high state of the MSB of the output, regardless of the data in the array.
     * Address: All addresses, usually un-programmed.
     * Voltage: Nominal VDD voltage supply level.
     * 
     * */
    task word_line_continuity_test ();
        bit[11:0] data = 12'b0;
        bit[11:0] adr = 12'b0;
		log_sim_description("1.3  Word-line continuity test", LOG_LEVEL_SEQUENCE);
        //TMODE high
        jtag_enable_with_tdo();
        // switch system clock to CLK       
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'hb2;
                dr_value == 266'h0;  dr_length == 0; init_jtag == 1'b0;})
        // Sel SA Test Mode N: MR[1]=1
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h02000000;   dr_length == 32; init_jtag == 1'b0;})
        // Set SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0400;   dr_length == 16; init_jtag == 1'b0;})       
        // Set AUTOINC, set EN_AUTO
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha0;
                dr_value == 266'h1001;   dr_length == 16; init_jtag == 1'b0;})
        // read data from OTP 12 bit data, 12 bit adr
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'h000aaa; dr_length == 24; init_jtag == 1'b0;})
        
        for (int i =0; i<=4095; i++) begin
            adr = i[11:0];
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
            		dr_value == 266'({data, adr});    dr_length == 24; init_jtag == 1'b0;})
            if (jtag_trans.read_dr !== 266'h800) begin
                `uvm_error(this.get_type_name(), $sformatf("Word line continutiy test error, data at addr %h is not as expected, got: %h expected: 12'h800",i , jtag_trans.read_dr))            
            end             
            //wait for 250ns
            #250ns;
            
        end //for-loop
        // reset MR 
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h00000000;   dr_length == 32; init_jtag == 1'b0;})       
        // reset SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        // reset AUTOINC, set EN_AUTO
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha0;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})
        
		#2us;
		// TMODE low
        jtag_disable();
        `uvm_info(get_type_name(), "end task: word_line_continuity_test", UVM_MEDIUM)       
    endtask : word_line_continuity_test 
    
    /*###   1.4 bit-line continuity test   ######################################################
     * 
     * To ensure continuity of all bit-lines and verify column decoding.
     * Set MR[2]=1 (BL Test Mode). This turns on the precharge high circuits at the far end of the bitlines.
     * A single-ended read operation should output all '1's at the selected read address regardless
     * of the memory contents.
     * Address: addresses[11:4], un-programmed or programmed.
     * Voltage: Nominal VDD voltage supply level.
     * 
     * */
    task bit_line_continuity_test ();
        bit[11:0] data = 12'b0;
        bit[11:0] adr = 12'b0;      
		log_sim_description("1.4  bit-line continuity test", LOG_LEVEL_SEQUENCE);
        //TMODE high
        jtag_enable_with_tdo();
        // switch system clock to CLK       
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'hb2;
                dr_value == 266'h0;  dr_length == 0; init_jtag == 1'b0;})
        // set bit-line continuity test: MR[2]=1
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h04000000;   dr_length == 32; init_jtag == 1'b0;})
        // Set SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0400;   dr_length == 16; init_jtag == 1'b0;})
        // read data from OTP 12 bit data, 12 bit adr
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'haaa000; dr_length == 24; init_jtag == 1'b0;})
        
        for (int i ='h010; i<=4095; i++) begin
            data = 12'b000;
            adr = i[11:0];
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
            		dr_value == 266'({data, adr});    dr_length == 24; init_jtag == 1'b0;})
            if (jtag_trans.read_dr !== 266'hfff) begin
                `uvm_error(this.get_type_name(), $sformatf("Word line continutiy test error, data at addr %h is expected 12'hfff but we got: %h", i, jtag_trans.read_dr))           
            end
            //wait for 250ns
            #250ns;
        end
        // reset MR 
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h00000000;   dr_length == 32; init_jtag == 1'b0;})       
        // reset SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        
		#2us;
		// TMODE low
        jtag_disable();
        `uvm_info(get_type_name(), "end task: bit_line_continuity_test", UVM_MEDIUM)
    endtask : bit_line_continuity_test
    
    
    /*###   1.5 Programm cell stress test  ######################################################
     * 
     * To expose all the memory cells to the maximum programming voltage conditions to activate leaky
     * bits.
     * Cycle through all row addresses A[m-2:1] of an un-programmed memory array with dummy
     * programming cycles (no data selected for programming). Use differential -redundant read mode
     * for faster test time. Use nomiinal short programming pulse width with the VPPmax/VRRmin
     * conditions.
     * 
     * */
    task program_cell_stress_test();
        bit[11:0] data = 12'b0;
        bit[11:0] adr = 12'b0;
		log_sim_description("1.5 Programm cell stress test", LOG_LEVEL_SEQUENCE);
        //TMODE high
        jtag_enable_with_tdo();
        // switch system clock to CLK       
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'hb2;
                dr_value == 266'h0;  dr_length == 0; init_jtag == 1'b1;})
        // set VPP level to max: MPP[3]=1 MPP[1]=1
        // set VRR level to min: MRR[3]=1 MRR[0]=1
        // set Differantial-Redundant: MR[4]=1 MR[0]=1
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h1100_090A;  dr_length == 32; init_jtag == 1'b0;})
        // Set SEL_MR
        // Set MRR,
        // Set SEL_MPP, Stress
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0720;   dr_length == 16; init_jtag == 1'b0;})       
        // Set adr=0

        for (int i ='h000; i<=(c_otp_array_size/4-1); i=i+2) begin
            adr = i[11:0];
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha2;
            		dr_value == 266'({adr, data});    dr_length == 24; init_jtag == 1'b0;})
            //wait for 120us
            #120us;
        end
        // reset MR 
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h00000000;   dr_length == 32; init_jtag == 1'b0;})       
        // reset SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        
		#2us;
		// TMODE low
        jtag_disable();
        `uvm_info(get_type_name(), "end task: program_cell_stress_test", UVM_MEDIUM)
    endtask : program_cell_stress_test

    
    /*###   1.6 Read cell stress test   ######################################################
     * 
     * To expose all the memory cells to the maximum read voltage conditions to activate leaky bits.
     * Reading the OTP memory cells using the array clean test directly after this read cell stress test
     * should reveal any leaky bits.
     * Cycle un-programmed memory array through all row addresses A[m-2:1] with read cycles
     * 
     * */
    task read_cell_stress_test();
        bit[11:0] data = 12'b0;
        bit[11:0] adr = 12'b0;
		log_sim_description("1.6 Read cell stress test", LOG_LEVEL_SEQUENCE);
		if (!uvm_hdl_force({ `STRING_OF(`OTP_INST),".core.test_trp_max"}, 1'b0))
			`uvm_error(this.get_type_name(), $sformatf("forcing of %s was not successful", { `STRING_OF(`OTP_INST),".core.test_trp_max"}))
		
        //TMODE high
        jtag_enable_with_tdo();
        // switch system clock to CLK       
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'hb2;
                dr_value == 266'h0;  dr_length == 0; init_jtag == 1'b0;})
        // set VRR level to max: MRR[2]=1 MRR[1]=1
        // set Differantial-Redundant: MR[4]=1 MR[0]=1
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h11000600;   dr_length == 32; init_jtag == 1'b0;})
        // Set SEL_MR
        // Set SEL_MRR,
        // Set SEL_TRP
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0640;   dr_length == 16; init_jtag == 1'b0;})
        // set read pulse to 5us
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha7;
                dr_value == 266'h003c;   dr_length == 16; init_jtag == 1'b0;})
        // read data from OTP
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'h000;  dr_length == 24; init_jtag == 1'b0;})
        // for...   
        for (int i=0; i<=2048; i=i+2) begin
            adr = i[11:0];
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
            		dr_value == 266'({adr, data});    dr_length == 24; init_jtag == 1'b0;})
            //wait for 250ns
            #250us;
        end

        // reset MR 
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h0000_0000;  dr_length == 32; init_jtag == 1'b0;})       
        // reset SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        
		#2us;
		// TMODE low
        jtag_disable(); 
        `uvm_info(get_type_name(), "end task: read_cell_stress_test", UVM_MEDIUM)
    endtask : read_cell_stress_test
    
    
    /*###   1.7 Array clean test   ######################################################
     * 
     * To find leaky cells and BL shorts revealed by the cell stress tests. If a leaky column (or BL) is
     * detected the part must be rejected.
     * Read all un-programmed address locations using VDDmin, VRRmax and maximum read pulse
     * width.
     * 
     * */
    task array_clean_test();
        bit[11:0] data = 12'b0;
        bit[11:0] adr = 12'b0;
		log_sim_description("1.7 Array clean test", LOG_LEVEL_SEQUENCE);
        //TMODE high
        jtag_enable_with_tdo();
        // switch system clock to CLK       
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'hb2;
                dr_value == 266'h0;  dr_length == 0; init_jtag == 1'b0;})
        // set VRR level to max: MRR[2]=1 MRR[1]=1
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h0000_0600;  dr_length == 32; init_jtag == 1'b0;})
        // Set SEL_MRR,
        // Set SEL_TRP
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0240;   dr_length == 16; init_jtag == 1'b0;})
        // set read pulse to 2.5us (OTP_READ_Config_Register)
        // The oscillator is untrimmed and running with 12 MHz so we have to use 30 (hex 1e) as value for tRP
        // for 18MHz use 90 (hex 2c)
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha7;
                dr_value == 266'h001e;   dr_length == 16; init_jtag == 1'b0;})
        // read data from OTP
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
                dr_value == 266'h000_000;  dr_length == 24; init_jtag == 1'b0;})
        // set AUTOINC,
        // set EN_AUTO
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha0;
                dr_value == 266'h1001;   dr_length == 16; init_jtag == 1'b0;})
        // for...   
        for (int i=0 ; i<= c_otp_array_size-1 ; i++) begin
            adr = i[11:0];
            `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha4;
            		dr_value == 266'({adr, data});    dr_length == 24; init_jtag == 1'b0;})
            //wait for 250ns
            #1us;
        end //for-loop
        // reset MR 
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha1;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        // reset SEL_MR
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha6;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})       
        // reset AUTOINC, set EN_AUTO
        `uvm_do_on_with(jtag_trans, m_jtag_master_agent.m_sequencer, { ir_length == 8; ir_value == 'ha0;
                dr_value == 266'h0000;   dr_length == 16; init_jtag == 1'b0;})
        `uvm_info(get_type_name(), "end task: array_clean_test", UVM_MEDIUM)
    endtask : array_clean_test
    
endclass
