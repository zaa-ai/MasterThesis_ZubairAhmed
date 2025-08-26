
class ic_startup_seq extends base_dsi_master_seq;
    
    `uvm_object_utils(ic_startup_seq)
    
    function new(string name = "");
        super.new("ic_startup");
    endfunction
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        log_sim_description("Testcase for IC startup procedure", LOG_LEVEL_TOP);
        
        startup_with_vcc_uv();
        startup_with_cldo_uv_ignore();
        startup_with_vrr_uv();
        startup_with_vrr_uv_ignore();
        
        too_early_start_crm();
        too_early_start_pdcm();
        
        startup_with_vcc_uv_ignore();
		access_ram_during_startup();
    endtask
    
    task startup_with_vcc_uv();
        log_sim_description($sformatf("startup with under voltage at VCC"), LOG_LEVEL_SEQUENCE);
        set_vcc_uv(1'b1);
        do_reset();
        #2ms;
        registers.check_flag(regmodel.Supply.supply_registers.SUP_STAT.VCCUV, 1'b1); 
        check_dsi_voltages_for_all_channels(1'b0);
        check_rfc(1'b0);
        // OTP must not be read
        registers.check_register(regmodel.Timebase.time_base_registers.TRIM_OSC, regmodel.Timebase.time_base_registers.TRIM_OSC.get_reset());
        
        set_vcc_uv(1'b0);
        #500us;
        check_ready();
    endtask
    
    task startup_with_vcc_uv_ignore();
        log_sim_description($sformatf("startup with under voltage at VCC and IGNORE_HWF"), LOG_LEVEL_SEQUENCE);
        set_vcc_uv(1'b1);
        do_reset();
        #2ms;
        registers.check_flag(regmodel.Supply.supply_registers.SUP_STAT.VCCUV, 1'b1); 
        check_dsi_voltages_for_all_channels(1'b0);
        check_rfc(1'b0);
        // OTP must not be read
        registers.check_register(regmodel.Timebase.time_base_registers.TRIM_OSC, regmodel.Timebase.time_base_registers.TRIM_OSC.get_reset());
        registers.write_and_check_field(regmodel.Supply.supply_registers.SUP_HW_CTRL.IGNORE_HWF, 1); 
        
        #500us;
        check_ready();
        set_vcc_uv(1'b0);
    endtask
    
    task startup_with_cldo_uv_ignore();
        log_sim_description($sformatf("startup with under voltage at CLDO and IGNORE_UV"), LOG_LEVEL_SEQUENCE);
        do_reset();
        set_cldo_uv(1'b1);
        #2ms;
        registers.check_flag(regmodel.Supply.supply_registers.SUP_STAT.LDOUV, 1'b1);
        check_dsi_voltages_for_all_channels(1'b0);
        check_rfc(1'b0);
        
        registers.write_and_check_field(regmodel.Supply.supply_registers.SUP_HW_CTRL.IGNORE_UV, 1); 
        #300us;
        check_ready();
        
        set_cldo_uv(1'b0);
        #100us;
        registers.check_flag(regmodel.Supply.supply_registers.SUP_STAT.LDOUV, 1'b0);
    endtask
    
    task startup_with_vrr_uv();
        log_sim_description($sformatf("startup with under voltage at VRR"), LOG_LEVEL_SEQUENCE);
        set_ref_fail(1'b1);
        do_reset();
        #2ms;
        registers.check_flag(regmodel.Supply.supply_registers.SUP_STAT.REF_FAIL, 1'b1); 
        check_dsi_voltages_for_all_channels(1'b0);
        check_rfc(1'b0);
        
        set_ref_fail(1'b0);
        #500us;
        check_ready();
    endtask
    
    task startup_with_vrr_uv_ignore();
        log_sim_description($sformatf("startup with under voltage at VRR (REF_FAIL) and IGNORE_HWF"), LOG_LEVEL_SEQUENCE);
        do_reset();
        set_ref_fail(1'b1);
        #2ms;
        registers.check_flag(regmodel.Supply.supply_registers.SUP_STAT.REF_FAIL, 1'b1);
        check_dsi_voltages_for_all_channels(1'b0);
        check_rfc(1'b0);
        
        registers.write_and_check_field(regmodel.Supply.supply_registers.SUP_HW_CTRL.IGNORE_HWF, 1); 
        #300us;
        check_ready();
        
        set_ref_fail(1'b0);
        #100us;
        registers.check_flag(regmodel.Supply.supply_registers.SUP_STAT.REF_FAIL, 1'b0);
    endtask
    
    task too_early_start_crm();
        get_checker_config().enable_spi_miso_crc_check = 1'b0;
        
        log_sim_description("start CRM before RFC", LOG_LEVEL_SEQUENCE);
        do_reset();
		transaction_recorder.enable_recorder();
        #300us;
        
        `spi_frame_begin
        	`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
       	    `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #1500us;
        
        get_checker_config().enable_spi_miso_crc_check = 1'b1;
        
        `spi_frame_begin
        	`spi_frame_create(spi_reset_seq,)
        `spi_frame_end
		
		transaction_recorder.expect_tr_count_for_all_channels(0);
		registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 1'b1);
        
        `spi_frame_begin
        	`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
        	`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end_with_status({SCI, NT0, NT1})
        
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff); // clear SPI IRQ
        `spi_frame_begin
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end_with_status({NT0, NT1})
        
		transaction_recorder.disable_recorder();
        #100us;
        read_crm_and_pcdm_data();
    endtask
    
    task too_early_start_pdcm();
        get_checker_config().enable_spi_miso_crc_check = 1'b0;
        
        log_sim_description("start PDCM before RFC", LOG_LEVEL_SEQUENCE);
        do_reset();
		transaction_recorder.enable_recorder();
        #300us;
        
        `spi_frame_begin
        	`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
        	`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #500us;
        
        get_checker_config().enable_spi_miso_crc_check = 1'b1;
        
        `spi_frame_begin
       		`spi_frame_create(spi_reset_seq,)
        `spi_frame_end
		
		transaction_recorder.expect_tr_count_for_all_channels(0);
		registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 1'b1);
        
        `spi_frame_begin
       		`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
       		`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end_with_status({SCI, NT0, NT1})
      
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff); // clear SPI IRQ
        `spi_frame_begin
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end_with_status({NT0, NT1})
        
		transaction_recorder.disable_recorder();
        #100us;
        read_crm_and_pcdm_data();
    endtask
    
    task do_reset();
        set_clock_ref(.enable(1'b0)); // against timing violations which can be avoided but are not relevant for design
        #10us;
        set_resb(0);
        #10us;
        set_clock_ref(.enable(1'b1));
        #90us;
        set_resb(1); 
    endtask
    
    task check_ready();
        check_dsi_voltages_for_all_channels(1'b1);
        check_rfc(1'b1);
        read_crm_and_pcdm_data();
    endtask
    
    task read_crm_and_pcdm_data();
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1; )
        `create_and_send_with(spec_measurement_command_stack_seq, )
	endtask
	
	
	task access_ram_during_startup();
		log_sim_description($sformatf("access RAM during startup"), LOG_LEVEL_SEQUENCE);
		set_vsup(4, 20us);
		do_reset();
		#100us;		
		for (int ram_offset=0; ram_offset < 10; ram_offset++) begin
			`spi_frame_begin
				`spi_frame_create(spi_read_master_register_seq, address == 12'(project_pkg::BASE_ADDR_RAM + ram_offset); burst_addresses.size()==0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end  
		end
		set_vsup(12, 20us);
		#500us;
		// reading un-initialized RAM must not result in an ECC error
		registers.check_flag(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.RAM, 1'b0);
		check_ic_revision();
	endtask
    
endclass
