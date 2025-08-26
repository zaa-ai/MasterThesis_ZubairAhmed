/**
 * Class: ecc_command_control_error_seq
 * 
 * sequence for applying ecc errors in command control block
 */
class ecc_command_control_error_seq extends ecc_error_base_seq;
    
    `uvm_object_utils(ecc_command_control_error_seq)
    
    event	finished_configuration;
    event	finished_wait_after_configuration;
    protected logic firstFrameAfterErrorValid = 1'b0;
    protected logic expectedInvalidatedTdmaScheme = 1'b0;
    
    function new(string name = "ecc_command_control_error");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_CMD;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_CMD;
        path = $sformatf(PATH_RAM_DATA_READ_ECC);
        test = "command control read operation with forcing";
        is_single_channel = 1'b1;
    endfunction
    
    logic[15:0]	command;
    virtual function void save_command(spi_dsi_command_seq _seq);
        command = _seq.get_word(0);
    endfunction
    
    virtual task apply_stimuli();
        tdma_scheme schemes[project_pkg::DSI_CHANNELS-1:0];
        spi_pdcm_seq	pdcm_seq;
        spi_read_pdcm_frame_seq read;
        tdma_scheme_pdcm scheme;
        bit all_channels_correct = (bit_error != TWO_BIT_ERR) ? 1'b1 : 1'b0;
        
        transaction_recorder.enable_recorder();
        transaction_recorder.clear_all();
        
        check_dab(1'b1);
        
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            dsi3_pdcm_packet	packet;
            
            packet = create_random_packet(.symbol_count(12), .sid(dsi3_pkg::sid_length_e'(1)));
            scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet);
            scheme.pdcm_period = 'd500;
            schemes[selected_channel] = scheme;
            schemes[selected_channel].packets[0].packet = scheme.packets[0].packet;
            schemes[selected_channel].packets[0].earliest_start_time = scheme.packets[0].earliest_start_time;
            schemes[selected_channel].packets[0].latest_start_time = scheme.packets[0].latest_start_time;
            schemes[selected_channel].packets[0].tolerance_int_min = 1000;
            schemes[selected_channel].packets[0].tolerance_int = 1000;
            schemes[selected_channel].packets[0].tolerance_int_max = 1000;
            `upload_tdma_scheme_with(scheme, channels == (2'b1 << selected_channel);)
            scheme.packets[0].earliest_start_time = scheme.packets[0].earliest_start_time + 5;
            scheme.packets[0].latest_start_time = scheme.packets[0].latest_start_time - 5;
            set_tdma_scheme_pdcm(selected_channel, scheme);
        end
        
        #10us;
        `spi_frame_begin
        -> finished_configuration;
        `spi_frame_send(pdcm_seq, channel_bits=='1; pulse_count == 8'd1;)
        //frame.finish_with_csn_active = 1'b0;
        save_command(pdcm_seq);
        `uvm_info(this.get_type_name(), $sformatf("Finished configuration event!"), UVM_INFO)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        #50us;
        `uvm_info(this.get_type_name(), $sformatf("Finished after configuration event!"), UVM_INFO)
        -> finished_wait_after_configuration;
        `spi_frame_end
        
        #700us;
        
        if (bit_error ==  TWO_BIT_ERR && firstFrameAfterErrorValid == 1'b0) begin
            check_dab(1'b1);
            if(expectedInvalidatedTdmaScheme == 1'b1) begin
                for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
                    tdma_scheme_upload_listener::invalidate(selected_channel);
                    clear_slave_pdcm_scheme_fifo(selected_channel);
                end
            end
        end
        else begin
            check_dab(1'b0);
        end
        
        `spi_frame_begin
        `spi_frame_send(read, channel_bits == 2'b11;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        // check results
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            if (bit_error ==  TWO_BIT_ERR && firstFrameAfterErrorValid == 1'b0) begin
                if(expectedInvalidatedTdmaScheme == 1'b1) begin
                    spi_read_status_seq status_seq; 
                    `spi_frame_begin
                    `spi_frame_send(status_seq, )
                    `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
                    `spi_frame_end_with_status({NT0, NT1})
                    status_seq.check_status_flags({NT0, NT1});
                end
                else begin
                    transaction_recorder.expect_tr_count(selected_channel, 0);
                    read.expect_empty(2'(selected_channel), 0);
                    clear_slave_crm_scheme_fifo(selected_channel);
                end
            end
            else begin
                transaction_recorder.expect_tr_count(selected_channel, 1);
                read.expect_flags( 2'(selected_channel), 0, schemes[selected_channel].packets[0].packet.crc_correct ? {} : {CRC});
                read.expect_packet_data(2'(selected_channel), 0, 0, schemes[selected_channel].packets[0].packet.get_word(0));
            end
        end
        check_dab(1'b1);
        
    endtask
    
    virtual function int get_field_mask();
        if (bit_error == ONE_BIT_ERR)
            return 'ha000; //additional writes on SRAM from command control will result in SRAM error
        else
            return 'h2000;
    endfunction
    
    virtual task apply_error();
        @(finished_wait_after_configuration);
        #(2.4us);
        apply_ecc_failure();
        fork
            begin
                @(negedge intb.D);
            end
            begin
                #5ms;
                `uvm_error(this.get_type_name(), $sformatf("INTB did not go to LOW"))
            end
        join_any
        disable fork;
        //		#1us;
        //		m_spi_agent.m_config.vif.CSN = 1'b1;
        //		#0.3us;
        remove_ecc_failure();
        #10us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(6)	ecc_error;
        logic[15:0]	ecc;
        ecc = ECC_pkg::DWF_ecc_gen_chkbits(16, 6, command);
        
        ecc_error = new(ecc[5:0], bit_error);
        if (!ecc_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        //FIXME: deposit is not working -> must be a static force but this will influence all read operations on RAM
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, ecc_error.get_data()), UVM_INFO)
        if (! uvm_hdl_force(path, ecc_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/*
 * Class: ecc_command_control_error_registers_seq
 * 
 * sequence for applying ecc errors in command control blocks registers
 */
class ecc_command_control_error_registers_seq extends ecc_command_control_error_seq;
    
    `uvm_object_utils(ecc_command_control_error_registers_seq)
    
    rand logic whileCmdsPresent;
    
    function new(string name = "ecc_command_control_error_registers_seq");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_CMD;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_CMD;
        path = $sformatf(PATH_COMMAND_CONTROL_CHANNELS);
        test = "command control channels register forcing";
        is_single_channel = 1'b1;
    endfunction
    
    virtual task apply_stimuli();
        spi_read_crm_data_packets_seq read;
        dsi3_crm_packet packets[$];

        transaction_recorder.enable_recorder();
        transaction_recorder.clear_all();
        
        create_valid_CRM_packets_with_data(packets);
        
        firstFrameAfterErrorValid = ~whileCmdsPresent;
        
        `uvm_info(this.get_type_name(), $sformatf("whileCmdsPresent = %0b!", whileCmdsPresent), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("First frame valid = %0b!", firstFrameAfterErrorValid), UVM_INFO)
        
        #5us;
        
        -> finished_configuration;
        `uvm_info(this.get_type_name(), $sformatf("Finished configuration event!"), UVM_INFO)
        
        #5us;
        
        check_dab(1'b1);
        
        `spi_frame_begin
            `spi_frame_create(spi_crm_seq, channel_bits=='1; broad_cast == 1'b0; )
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
            `uvm_info(this.get_type_name(), $sformatf("Finished after configuration event!"), UVM_INFO)
        `spi_frame_end
         -> finished_wait_after_configuration;
        
        #700us;
        
        if (bit_error ==  TWO_BIT_ERR && firstFrameAfterErrorValid == 1'b0) begin
            check_dab(1'b1);
        end
        else begin
            check_dab(1'b0);
        end
        
        `spi_frame_begin
            `spi_frame_send(read, channel_bits == 2'b11;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end

        // check results
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
          if (bit_error ==  TWO_BIT_ERR && firstFrameAfterErrorValid == 1'b0) begin
              transaction_recorder.expect_tr_count(selected_channel, 0);
              read.expect_empty(2'(selected_channel));
              clear_slave_crm_scheme_fifo(selected_channel);
          end
          else begin
                transaction_recorder.expect_tr_count(selected_channel, 1);
                read.expect_flags( 2'(selected_channel), packets[selected_channel].crc_correct ? {} : {CRC});
                read.expect_packet(2'(selected_channel), packets[selected_channel]);
          end
        end
        check_dab(1'b1);
        
    endtask
    
    virtual task apply_error();
        if(whileCmdsPresent == 1'b1) begin
            @(finished_wait_after_configuration);
            `uvm_info(this.get_type_name(), $sformatf("THIS!"), UVM_INFO)
            #300ns;
        end
        else begin
            @(finished_configuration);
            `uvm_info(this.get_type_name(), $sformatf("THAT!"), UVM_INFO)
        end
        apply_ecc_failure();
        fork
            begin
                @(negedge intb.D);
            end
            begin
                #5ms;
                `uvm_error(this.get_type_name(), $sformatf("INTB did not go to LOW"))
            end
        join_any
        disable fork;
        remove_ecc_failure();
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
    endtask
    
    virtual function int get_field_mask();
        int mask;
        if (is_single_channel == 1'b1)
            mask = 1 << (irq_stat_ecc_field.get_lsb_pos());
        else
            mask = 1 << (irq_stat_ecc_field.get_lsb_pos() + channel);
        $display("mask=%4h", mask);
        return mask;
    endfunction
    
endclass : ecc_command_control_error_registers_seq

/*
 * Class: ecc_command_control_error_channels_seq
 * 
 * sequence for applying ecc errors in command control blocks channel register
 */
class ecc_command_control_error_channels_seq extends ecc_command_control_error_registers_seq;
    
    `uvm_object_utils(ecc_command_control_error_channels_seq)
    
    function new(string name = "ecc_command_control_error_channels");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_CMD;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_CMD;
        path = $sformatf(PATH_COMMAND_CONTROL_CHANNELS);
        test = "command control channels register forcing";
        is_single_channel = 1'b1;
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(2)   ecc_error;
        uvm_hdl_data_t  data;
        
        if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
        else `uvm_info(this.get_type_name(), $sformatf("read %s with 0x%0h", path, data[1:0]), UVM_INFO)    
        
        ecc_error = new(data[1:0], bit_error);
        if (!ecc_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        if (! uvm_hdl_deposit(path, ecc_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("force %s with %0h", path, ecc_error.get_data()), UVM_INFO)
        
    endtask
    
endclass : ecc_command_control_error_channels_seq

/*
 * Class: ecc_command_control_error_command_counter_seq
 * 
 * sequence for applying ecc errors in command control blocks command_counter register
 */
class ecc_command_control_error_command_counter_seq extends ecc_command_control_error_registers_seq;
    
    `uvm_object_utils(ecc_command_control_error_command_counter_seq)
    
    function new(string name = "ecc_command_control_error_command_counter");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_CMD;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_CMD;
        path = $sformatf(PATH_COMMAND_CONTROL_COMMAND_COUNTER);
        test = "command control channels register forcing";
        is_single_channel = 1'b1;
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(4)   ecc_error;
        uvm_hdl_data_t  data;
        
        if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
        else `uvm_info(this.get_type_name(), $sformatf("read %s with 0x%0h", path, data[3:0]), UVM_INFO)    
        
        ecc_error = new(data[3:0], bit_error);
        if (!ecc_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        if (! uvm_hdl_deposit(path, ecc_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("force %s with %0h", path, ecc_error.get_data()), UVM_INFO)
        
    endtask
    
endclass : ecc_command_control_error_command_counter_seq

/*
 * Class: ecc_command_control_error_jtag_ecc_inject_seq
 * 
 * sequence for applying ecc errors in command control block with JTAG module using ECC modify registers
 */
class ecc_command_control_error_jtag_ecc_inject_seq extends ecc_command_control_error_seq;
    
    rand int unsigned	bit_position;
    constraint c_bit {bit_position < project_pkg::ECC_WIDTH; }
    
    `uvm_object_utils(ecc_command_control_error_jtag_ecc_inject_seq)
    
    function new(string name = "");
        super.new("ecc_command_control_error_jtag_ecc_inject_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.RAM;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.RAM;
        test = "command control read operation with JTAG using ECC modify";
    endfunction
    
    virtual task apply_error();
        @(finished_configuration);
        #(2.4us);
        apply_ecc_failure();
        fork
            begin
                @(negedge intb.D);
            end
            begin
                #5ms;
                `uvm_error(this.get_type_name(), $sformatf("INTB did not go to LOW"))
            end
        join_any
        disable fork;
        remove_ecc_failure();
        #10us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(6)	ecc_error;
        ecc_error = new(0, bit_error);
        if (!ecc_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        `uvm_info(this.get_type_name(), $sformatf("Enable JTAG"), UVM_INFO)
        jtag_enable(.initialize_jtag(1'b1));
        #0.1us;
        test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_ECC_CONTROL.ELIP_ECC.write(status, ecc_error.get_data());
        
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("Disable JTAG"), UVM_INFO)
        jtag_disable();
    endtask
    
endclass

/*
 * Class: ecc_command_control_error_jtag_ecc_swap_seq
 * 
 * sequence for applying ecc errors in command control block with JTAG module using ECC swap bit
 */
class ecc_command_control_error_jtag_ecc_swap_seq extends ecc_command_control_error_seq;
    
    rand int unsigned	bit_position;
    constraint c_bit {bit_position < project_pkg::ECC_WIDTH; }
    
    `uvm_object_utils(ecc_command_control_error_jtag_ecc_swap_seq)
    
    function new(string name = "");
        super.new("ecc_command_control_error_jtag_ecc_swap_seq");
        issues_only_double_error = 1'b1;
        expectedInvalidatedTdmaScheme = 1'b1;
    endfunction
    
    virtual function void initialize();
        super.initialize();
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.RAM;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.RAM;
        test = "command control read operation with JTAG using ECC swap";
    endfunction
    
    virtual task apply_error();
        @(finished_configuration);
        apply_ecc_failure();
        fork
            begin
                @(posedge spi.CSN);
                @(posedge spi.CSN);
            end
            begin
                #5ms;
                `uvm_error(this.get_type_name(), $sformatf("INTB did not go to LOW"))
            end
        join_any
        disable fork;
        remove_ecc_failure();
        #10us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task apply_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("Enable JTAG"), UVM_INFO)
        jtag_enable(.initialize_jtag(1'b1));
        #1us;
        test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_ECC_CONTROL.SRAM_ECC_SWAP.write(status, 1'b1);
        #5us;
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("Disable JTAG"), UVM_INFO)
        jtag_disable();
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        if (bit_error == TWO_BIT_ERR) begin 
            `create_and_send(single_crm_on_all_channels_all_fail_seq)
            `create_and_send(single_pdcm_on_all_channels_fail_seq)
        end
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
    virtual function int get_field_mask();
        int mask;
        mask = 1 << (irq_stat_ecc_field.get_lsb_pos());
        return mask;
    endfunction
    
endclass

/*
 * Class: ecc_command_control_error_jtag_ecc_sel_val_seq
 * 
 * sequence for applying ecc errors in command control block with JTAG module using ECC SEL/VAL
 */
class ecc_command_control_error_jtag_ecc_sel_val_seq extends ecc_command_control_error_seq;
    
    `uvm_object_utils(ecc_command_control_error_jtag_ecc_sel_val_seq)
    
    function new(string name = "");
        super.new("ecc_command_control_error_jtag_ecc_sel_val_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        test = "command control read operation with JTAG using ECC sel/val";
        issues_only_double_error = 1'b1;
        expectedInvalidatedTdmaScheme = 1'b1;
    endfunction
    
    virtual task apply_stimuli();
        
        super.apply_stimuli();
    endtask
    
    virtual task apply_error();
        @finished_configuration;
        apply_ecc_failure();
        #2us;
        m_spi_agent.m_config.vif.CSN = 1'b1;
        #10us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // ECC Failures might lead to HW_FAIL due to wrongly decoded command in command_control, therefore reset HW_FAIL IRQ
            regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.HW_FAIL, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task apply_ecc_failure();
        jtag_read_elip_seq	read;
        logic[11:0]	ram_address;
        
        `uvm_info(this.get_type_name(), $sformatf("Enable JTAG"), UVM_INFO)
        jtag_enable_with_tdo(.initialize_jtag(1'b1));
        `uvm_do_on_with(read, m_jtag_master_agent.m_sequencer, {address == ADDR_SPI_CMD_STAT_BUF_WRITE_POINTER;})
        ram_address = read.read_value[11:0];
        
        @(finished_wait_after_configuration);
        #2us;
        `uvm_info(this.get_type_name(), $sformatf("Disable JTAG"), UVM_INFO)
        fork
            jtag_disable();    
        join_none
        
        `uvm_info(this.get_type_name(), $sformatf("Flipp SRAM Bit(s) for RAM address 0x%0h", ram_address), UVM_INFO)
        flipp_bits_in_sram(ram_address, bit_error);
        
    endtask
    
    virtual function int get_field_mask();
        return 'h8000;
    endfunction
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        if (bit_error == TWO_BIT_ERR) begin
            `create_and_send(single_crm_on_all_channels_all_fail_seq)
            `create_and_send(single_pdcm_on_all_channels_fail_seq)
        end
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass
