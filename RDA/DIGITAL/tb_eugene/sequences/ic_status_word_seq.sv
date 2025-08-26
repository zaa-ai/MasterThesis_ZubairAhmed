class ic_status_word_seq extends base_dsi_master_seq;
    
    `uvm_object_utils(ic_status_word_seq)
    
    function new(string name = "");
        super.new("ic_status_word");
    endfunction
    
    virtual task run_tests();
        log_sim_description("Testcase for IC status word", LOG_LEVEL_TOP);
        
        send_only_status_in_a_frame();
        send_frame_with_status_and_crc_only();
        send_tx_crc_only();
        
        check_CR_channel_flags();
        check_PD_NT_channel_flags();
        
        check_hardware_error_flags();
        change_status_during_status_request();
        check_sup_stat_register();
        
        // do some communication to check normal behavior
        `spi_frame_begin
        `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
        `spi_frame_begin
        `spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        `create_and_send(spec_CRM_command_seq)
        `create_and_send(spec_single_frame_pdcm_read_seq) 
        
        // SCI, CRC is checked in spi_errors testcase
        // BF flag is checked in buffer control testcase
    endtask
    
    task send_only_status_in_a_frame();
        log_sim_description("send only IC status with TX CRC in a frame", LOG_LEVEL_SEQUENCE);
        
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 'hffff);
        
        `spi_frame_begin
        `spi_frame_create(spi_read_status_seq , )
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        check_IC_status_word_and_SPI_IRQ();
    endtask
    
    task check_IC_status_word_and_SPI_IRQ();
        #2us;
        `spi_frame_begin
        `spi_frame_create(spi_tx_crc_request_seq , mosi_crc_correct==1'b1; )
        `spi_frame_end_with_status({NT0, NT1})
        
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 0);
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 'hffff);
        #10us;
    endtask
    
    task send_frame_with_status_and_crc_only();
        bit crc_correct = 1'b1;
        
        repeat(2) begin
            crc_correct = ~crc_correct;
            log_sim_description($sformatf("send read status and TX CRC only in a frame with CRC %scorrect", crc_correct?"":"in" ), LOG_LEVEL_SEQUENCE);
            regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 'hffff);
            `spi_frame_begin
            `spi_frame_create(spi_read_status_seq, )
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
            `spi_frame_end
            check_IC_status_word_and_SPI_IRQ();
        end
    endtask
    
    task send_tx_crc_only();
        log_sim_description("send TX CRC only in a frame", LOG_LEVEL_SEQUENCE);
        
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 'hffff);
        `spi_frame_begin
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
        `spi_frame_end
        check_IC_status_word_and_SPI_IRQ();
    endtask
    
    /*
     * Check CR0, CR1
     */ 
    task check_CR_channel_flags();
        spi_read_crm_data_packets_seq read;
        spi_crm_seq crm_seq;
        
        log_sim_description("IC status word channel flags", LOG_LEVEL_SEQUENCE);
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            dsi3_crm_packet packet = new();
            if(!packet.randomize()) `uvm_error(this.get_name(), "randomization error")	
            
            log_sim_description($sformatf("check IC status word CR%0d flag", channel), LOG_LEVEL_OTHERS);
            
            add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(packet.get_word(0), packet.get_word(1)));
            
			check_ic_status({NT0, NT1});
            `spi_frame_begin
            `spi_frame_send(crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
            `spi_frame_end_with_status({NT0, NT1})
            
            #500us;
            
			check_ic_status(channel == 0 ? {NT0, NT1, CR0} : {NT0, NT1, CR1});
            
            `spi_frame_begin
            `spi_frame_send(read, channel_bits == 2'b01 << channel;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
            `spi_frame_end_with_status(channel == 0 ? {NT0, NT1, CR0} : {NT0, NT1, CR1})
            
			check_ic_status({NT0, NT1});
            
            read.expect_flags(2'(channel), packet.crc_correct ? {} : {CRC});
            read.expect_symbol_count(2'(channel), 8'd8);
            read.expect_packet(2'(channel), packet);
            #100us;
        end
    endtask
    
    /*
     * Check PD0, PD1, NT0, NT1
     */ 
    task check_PD_NT_channel_flags();
        log_sim_description("IC status word channel flags", LOG_LEVEL_SEQUENCE);
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            tdma_scheme_pdcm scheme = new();
            
            log_sim_description($sformatf("check IC status word PD%0d flag", channel), LOG_LEVEL_OTHERS);
            
            // invalidate any existing TDMA scheme
            `spi_frame_begin
                `spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
                `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
            `spi_frame_end
            
            #100us;
            
			check_ic_status({NT0, NT1});
            
            if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
            `upload_tdma_scheme_with(scheme, channels == 2'b01 << channel;)
            set_tdma_scheme_pdcm(channel, scheme);
            
            #100us;
            
			check_ic_status(channel == 0 ? {NT1} : {NT0});
            
            `spi_frame_begin
            `spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
            `spi_frame_end_with_status(channel == 0 ? {NT1} : {NT0})
            
            #(scheme.pdcm_period * 1us);
            
            #500us;
            
			check_ic_status(channel == 0 ? {NT1, PD0} : {NT0, PD1});
            
            `spi_frame_begin
            `spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
            `spi_frame_end_with_status(channel == 0 ? {NT1, PD0} : {NT0, PD1})
            
			check_ic_status(channel == 0 ? {NT1} : {NT0});
            #100us;
        end
        // invalidate any existing TDMA scheme
        `spi_frame_begin
            `spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #100us;
    endtask
    
    task check_hardware_error_flags();
        // disable automatic check for HE flag
        get_checker_config().enable_hardware_error_check = 1'b0;
        
        `create_and_send(hardware_error_overtemperature_seq)
        `create_and_send(hardware_error_clkref_error_seq)
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            `create_and_send_with(hardware_error_undervoltage_dsi_seq, 	channel==local::channel;)
            `create_and_send_with(hardware_error_undervoltage_dsi_with_deactivated_channels_seq, 	channel==local::channel;)
            `create_and_send_with(hardware_error_overvoltage_dsi_seq, 	channel==local::channel;)
            `create_and_send_with(hardware_error_overvoltage_dsi_with_deactivated_channels_seq, 	channel==local::channel;)
            `ifndef GATE_LEVEL
            `create_and_send_with(hardware_error_hw_fail_dsi_seq, 		channel==local::channel;)
			`create_and_send_with(hardware_error_hw_fail_dsi_iload_seq, channel==local::channel;)
            `create_and_send_with(hardware_error_hw_fail_dsi_core_seq, 	channel==local::channel;)
            `endif
            
			log_sim_description($sformatf("check hardware error flag HW_FAIL_DSI_COMMAND_BUFFER for channel %0d", channel), LOG_LEVEL_SEQUENCE);
            // wrong word count (two words are needed for DSI_WAIT)
            `create_and_send_with(hardware_error_hw_fail_dsi3_command_buffer_wrong_command_seq, wrong_command[15:12] == CMD_DSI_WAIT; wrong_command[11:10] == 2'b01 << channel; channel==local::channel;)
            repeat(10) begin
                logic[1:0] pdcm_channels = 2'($urandom_range(0, 3));
                pdcm_channels[channel] = 1'b0; // clear bit for current channel
                // wrong channel
                `create_and_send_with(hardware_error_hw_fail_dsi3_command_buffer_wrong_command_seq, wrong_command[15:12] == CMD_PDCM; wrong_command[11:10] == pdcm_channels; channel==local::channel;)
                // wrong command				
                `create_and_send_with(hardware_error_hw_fail_dsi3_command_buffer_wrong_command_seq, wrong_command[15:12] inside {CMD_STATUS_READ, CMD_TX_CRC, CMD_REG_READ, CMD_READ_CRM_PACKETS, CMD_READ_PDCM_PACKETS}; wrong_command[11:10] == 2'b01 << channel; channel==local::channel;)
            end
        end
        
        `create_and_send(hardware_error_undervoltage_vcc_seq)
        `create_and_send(hardware_error_undervoltage_cldo_seq)
        `create_and_send(hardware_error_ref_fail_seq)
        
        `ifndef GATE_LEVEL
        `create_and_send(hardware_error_hw_fail_spi_seq)
        `endif
        
        // repeat because there are different possibilities for a wrong state in command_control
        `ifndef GATE_LEVEL
			log_sim_description("check hardware error flag HW_FAIL_MAIN", LOG_LEVEL_SEQUENCE);
	        repeat(2) begin
	            `create_and_send(hardware_error_hw_fail_main_seq)
	        end
	        
			log_sim_description("check hardware error flag HW_FAIL_COMMAND_CONTROL", LOG_LEVEL_SEQUENCE);
	        repeat(10) begin
	            `create_and_send(hardware_error_hw_fail_command_control_seq)
	        end
        `endif
        
        // insert wrong commands into command buffer (these commands are executed by SPI directly)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_STATUS_READ;)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_TX_CRC;)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_REG_READ;)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_READ_CRM_PACKETS;)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_READ_PDCM_PACKETS;)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_RESET;)
		// some random combinations
		repeat(20) begin
            `create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command inside {CMD_STATUS_READ, CMD_TX_CRC, CMD_REG_READ, CMD_READ_CRM_PACKETS, CMD_READ_PDCM_PACKETS, CMD_RESET};)
        end
        
        // insert wrong command lengths into command buffer (these commands consist of more than 1 word)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_CRM;)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_DSI_WAIT;)
		`create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_UPLOAD_TDMA;)
		// some random combinations
        repeat(20) begin
            `create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command inside {CMD_CRM, CMD_DSI_WAIT, CMD_UPLOAD_TDMA};)
        end
        
        // wrong register write
        `create_and_send_with(hardware_error_hw_fail_command_control_wrong_command_seq, wrong_command == CMD_REG_WRITE; initial_command == CMD_PDCM;)
        
        get_checker_config().enable_hardware_error_check = 1'b1;
		#100us;
    endtask                        					
    
    task change_status_during_status_request();
        spi_read_status_seq status_seq[$];	
        log_sim_description("change IC status during status word commands", LOG_LEVEL_SEQUENCE);
        get_checker_config().enable_hardware_error_check = 1'b0;
        fork
            begin
                #10us set_ref_fail(1'b1);
                #100us;
                set_ref_fail(1'b0);
            end
            begin
                #65us;
                `spi_frame_begin
                for(int i=0; i< 200; i++) begin
                    `spi_frame_send(status_seq[i],)
                end
                `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                `spi_frame_end
            end
        join
        
        for(int i=0; i< 200; i++) begin
            if(i < 15 || i > 180) begin
                status_seq[i].status.check_status_flags({NT0, NT1});
            end
            if(i > 50 && i < 100) begin
                if(status_seq[i].status.get_value(HE) != 1'b1)  `uvm_error(this.get_name(), $sformatf("Unexpected value in status word command number %0d, expected HE flag, got none", i))
            end
        end
        #100us;
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    task check_sup_stat_register();
        uvm_reg_field ote = regmodel.Supply.supply_registers.SUP_STAT.OTE;
        uvm_reg_field otw = regmodel.Supply.supply_registers.SUP_STAT.OTW;
        uvm_reg_field ldouv = regmodel.Supply.supply_registers.SUP_STAT.LDOUV;
        uvm_reg_field vccuv = regmodel.Supply.supply_registers.SUP_STAT.VCCUV;
        uvm_reg_field ref_fail = regmodel.Supply.supply_registers.SUP_STAT.REF_FAIL;
        
        // disable automatic check for HE flag
        get_checker_config().enable_hardware_error_check = 1'b0;
        
        log_sim_description("check all flags of SUP_STAT register", LOG_LEVEL_SEQUENCE);
        
        log_sim_description("check OTW flag of SUP_STAT register", LOG_LEVEL_OTHERS);
        registers.check_register(regmodel.Supply.supply_registers.SUP_STAT, 0);
        set_temp(130, 10us);
        #100us;
        registers.check_flag(ote, 0);
        registers.check_flag(otw, 1);
        registers.check_flag(ldouv, 0);
        registers.check_flag(vccuv, 0);
        registers.check_flag(ref_fail, 0);
        set_temp(25, 10us);
        #100us;
        
        log_sim_description("check OTE flag of SUP_STAT register", LOG_LEVEL_OTHERS);
        registers.check_register(regmodel.Supply.supply_registers.SUP_STAT, 0);
        set_temp(175, 10us);
        #100us;
        registers.check_flag(ote, 1);
        registers.check_flag(otw, 1);
        registers.check_flag(ldouv, 1);
        registers.check_flag(vccuv, 0);
        registers.check_flag(ref_fail, 0);
        set_temp(25, 10us);
        #500us;
        regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
        
        log_sim_description("check LDOUV flag of SUP_STAT register", LOG_LEVEL_OTHERS);
        registers.check_register(regmodel.Supply.supply_registers.SUP_STAT, 0);
        set_cldo_uv(1'b1);
        #200us;
        registers.check_flag(ote, 0);
        registers.check_flag(otw, 0);
        registers.check_flag(ldouv, 1);
        registers.check_flag(vccuv, 0);
        registers.check_flag(ref_fail, 0);
        set_cldo_uv(1'b0);
        #500us;
        
        log_sim_description("check VCCUV flag of SUP_STAT register", LOG_LEVEL_OTHERS);
        registers.check_register(regmodel.Supply.supply_registers.SUP_STAT, 0);
        set_vcc_uv(1'b1);
        #200us;
        registers.check_flag(ote, 0);
        registers.check_flag(otw, 0);
        registers.check_flag(ldouv, 0);
        registers.check_flag(vccuv, 1);
        registers.check_flag(ref_fail, 1);
        set_vcc_uv(1'b0);
        #500us;
        
        log_sim_description("check REF_FAIL flag of SUP_STAT register", LOG_LEVEL_OTHERS);
        registers.check_register(regmodel.Supply.supply_registers.SUP_STAT, 0);
        set_ref_fail(1'b1);
        #200us;
        registers.check_flag(ote, 0);
        registers.check_flag(otw, 0);
        registers.check_flag(ldouv, 0);
        registers.check_flag(vccuv, 0);
        registers.check_flag(ref_fail, 1); 
        set_ref_fail(1'b0);
        #500us;
        
        registers.check_register(regmodel.Supply.supply_registers.SUP_STAT, 0);
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    task check_ic_status(spi_status_word_flags status_flags[$]);
        spi_read_status_seq status_seq;	
        `spi_frame_begin
        `spi_frame_send(status_seq, )
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
        `spi_frame_end_with_status(status_flags)
        status_seq.check_status_flags(status_flags);
        check_ic_status_register(status_flags);
    endtask
    
    task check_ic_status_register(spi_status_word_flags status_flags[$]);
        uvm_reg_data_t value;
        flags_container #(spi_status_word_flags) flags = new();
        flags.set_flags(status_flags);
        
        regmodel.SPI.SPI_registers.STATUS_WORD.read(status, value);
        if(flags.get_values() != int'(value)) `uvm_error(this.get_name(), $sformatf("Unexpected value in STATUS_WORD register, expected 0x%0h, got 0x%0h", flags.get_values(), value))
    endtask
    
endclass
