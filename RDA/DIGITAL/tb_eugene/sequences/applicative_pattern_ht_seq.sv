class intb_ht_pin extends digital_pin;
	function new(time period, virtual digital_signal_if _vif, string name);
		super.new(period, _vif, '{name}, 1);
		powered_up = 1'b1;
		x_before_edge = 30us;
		x_after_edge = 60us;
		_is_output = 1'b1;
        x_powerup = 1.11ms;
	endfunction
endclass

class applicative_pattern_ht_seq extends applicative_pattern_seq;
	
	`uvm_object_utils(applicative_pattern_ht_seq)

	function new(string name = "");
		super.new("applicative_pattern_ht");
        pattern_name = "applicative_pattern_ht";
        period = 100ns;
	endfunction
	
	virtual task run_tests();
        set_temp(140);
		power_up(0us);
		make_pattern();
		#100us;
	endtask
	
	virtual task make_pattern();
        set_clock_ref(.enable(0));
		initialize();
		do_pattern();
		`uvm_info(this.get_type_name(), "writing pattern file", UVM_NONE);
		write_pattern();
		#1ms;
	endtask
	
	virtual function pattern_domain create_domain_MDM500(int period);
		pattern_domain domain;
		domain = new(period, "MdmDpins", "MDM500");
		begin : add_digital_signals
			digital_pin	signal;
			signal = bfwb_pin::new(period, bfwb, "BFWB");
			domain.add_signal(signal);
			signal = dab_pin::new(period, dab, "DAB");
			domain.add_signal(signal);
			signal = digital_input_pin::new(period, syncb, "SYNCB");
			domain.add_signal(signal);
			signal = intb_ht_pin::new(period, intb, "INTB");
			domain.add_signal(signal);
			signal = digital_input_pin::new(period, resb, "RESB");
			domain.add_signal(signal);
		end
		return domain;
	endfunction
	
	virtual task do_pattern();
        tdma_scheme_pdcm    scheme_pdcm;
        
        packets = new(.number_of_frames(NUMBER_OF_PDCM_FRAMES+1));
        
		foreach (dsi_voltages[i])	dsi_voltages[i].set_sampling(1'b0);
		spi_signals.set_sampling(1'b0);
		set_clock_ref(.enable(0));
		_pattern.start_sampling();
		#12ns;
		`uvm_info(this.get_type_name, "Starting pattern", UVM_NONE)
		
        check_resb_debouncer();
        get_checker_config().enable_hardware_error_check = 1'b0;
        
		#400us;
		comment_pattern("enable CLKREF input");
		set_clock_ref(.enable(1));
		#400us;

		fork
			#1300us;
			begin
                regmodel.Supply.supply_registers.SUP_IRQ_MASK.OTW.write(status, 0);
				make_buffer_full_and_set_BFBW_pin();
				configure_channels(dsi3_pkg::BITTIME_16US);
			end
		join
		
		spi_signals.set_sampling(1'b1);
		read_interrupts();
		reset_interrupts();
		
		// Jira P52143-483: SPI communication with CSB=1
        spi_communication_with_csb_high();
		
		foreach (dsi_voltages[i])	dsi_voltages[i].set_sampling(1'b1);
		#20us;
		
		set_TDMA_schemes();
		send_crm_command();
        send_crm_answer();
		
        upload_tdma_scheme(packets, scheme_pdcm);
        
		send_pdcm_command();
		
        send_pdcm_answer(packets, scheme_pdcm);
        
		read_data();
		
		read_interrupts();
        
        invalidate_TDMA();
		#1us;
		_pattern.stop_sampling();
		
		`uvm_info(this.get_type_name, "Ending pattern", UVM_NONE);
		
    endtask
    
	virtual task configure_channels(dsi3_pkg::dsi3_bit_time_e bit_time);
        uvm_reg_data_t read_value;
        int crm_duration = int'(320*dsi3_pkg::get_bit_time_factor(dsi3_pkg::BITTIME_16US) + 24*1.05*dsi3_pkg::CHIPTIME_3US + 30);
		comment_pattern($sformatf("set bit time to %s", bit_time.name()));
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, 1);
		comment_pattern($sformatf("set CRM_TIME to %s", crm_duration+70));
        regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME.TIME.write(status, crm_duration+70);
		comment_pattern($sformatf("read CRM_TIME"));
        regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME.TIME.read(status, read_value);
	endtask
	
endclass
