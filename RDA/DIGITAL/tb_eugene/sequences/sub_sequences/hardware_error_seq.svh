
class hardware_error_seq extends base_dsi_master_seq;
    
    rand int	channel;
	bit enable_sim_log = 1'b1;
    
    constraint co_channel {channel inside {[0:project_pkg::DSI_CHANNELS]};}
    
    `uvm_object_utils(hardware_error_seq)
    
    typedef enum bit {
        STATUS,
        IRQ
    } status_type_e;
    
    spi_status_word_flags	expected_flags[$];
    uvm_reg_field 			irq_field;
    status_type_e			status_type;
    string					error_name = "general hardware error";
    
    function new(string name = "");
        super.new(name);
        expected_flags.delete();
        expected_flags.push_back(HE);
        expected_flags.push_back(NT0);
        expected_flags.push_back(NT1);
        status_type = STATUS;
    endfunction
    
    virtual task run_tests();
        if(enable_sim_log == 1'b1) begin	
        	log_sim_description($sformatf("check hardware error flag %s", error_name), LOG_LEVEL_SEQUENCE);
		end
        
        irq_field.write(status, 1'b1); // initially clear IRQ in case its set during previous test
        check_ic_status({NT0, NT1}); // check that there is no error at the beginning
        registers.check_flag(irq_field, 1'b0);
        apply_error_condition();
        #200us;
        registers.check_flag(irq_field, 1'b1);
        check_ic_status(expected_flags); // check status + STATUS_WORD register
        release_error_condition();
        write_enables();
        #200us;
        if (status_type == IRQ) begin
            irq_field.write(status, 1'b1); // clear IRQ
            registers.check_flag(irq_field, 1'b0);
        end
        check_ic_status({NT0, NT1}); // check that there is no error at the end
        if (status_type == STATUS) begin
            irq_field.write(status, 1'b1); // clear IRQ
            registers.check_flag(irq_field, 1'b0);
        end
        
    endtask
    
    virtual task apply_error_condition();
        `uvm_error(this.get_type_name(), "DO NOT USE hardware_error_seq.apply_error_condition!")
    endtask
    
    virtual task release_error_condition();
        `uvm_error(this.get_type_name(), "DO NOT USE hardware_error_seq.release_error_condition!")
    endtask
    
    virtual task check_ic_status(spi_status_word_flags status_flags[$]);
        spi_read_status_seq status_seq;	
        `spi_frame_begin
        `spi_frame_send(status_seq, )
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
        `spi_frame_end
        status_seq.check_status_flags(status_flags);
        check_ic_status_register(status_flags);
    endtask
    
    virtual task check_ic_status_register(spi_status_word_flags status_flags[$]);
        uvm_reg_data_t value;
        flags_container #(spi_status_word_flags) flags = new();
        flags.set_flags(status_flags);
        
        regmodel.SPI.SPI_registers.STATUS_WORD.read(status, value);
        if(flags.get_values() != int'(value)) `uvm_error(this.get_name(), $sformatf("Unexpected value in STATUS_WORD register, expected 0x%0h, got 0x%0h", flags.get_values(), value))
    endtask
    
    virtual task write_enables();
        #100us;
        regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
    endtask
    
    virtual task jtag_write(int elip_address, int elip_data);
        jtag_write_elip_seq elip_write_seq;
        jtag_enable();
        #5us;
        `uvm_do_on_with(elip_write_seq, m_jtag_master_agent.m_sequencer, {address == elip_address; data == elip_data; init == 1;})
        #5us;
        jtag_disable();
        #5us;
    endtask
    
endclass

class hardware_error_overtemperature_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_overtemperature_seq)
    
    function new(string name = "");
        super.new("hardware_error_overtemperature");
        error_name = "OVERTEMPERATURE";
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTE;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        set_temp(175, 10us);
    endtask
    
    virtual task release_error_condition();
        set_temp(25, 10us);
    endtask
    
endclass

class hardware_error_clkref_error_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_clkref_error_seq)
    
    function new(string name = "");
        super.new("hardware_error_clkref_error");
        error_name = "CLKREF_FAILURE";
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.CLKREF;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        set_clock_ref(500000, 1'b0);
    endtask
    
    virtual task release_error_condition();
        set_clock_ref(500000, 1'b1);
    endtask
    
endclass

class hardware_error_undervoltage_dsi_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_undervoltage_dsi_seq)
    
    function new(string name = "");
        super.new("hardware_error_undervoltage_dsi");
        error_name = "UNDERVOLTAGE_DSI";
        status_type = IRQ;
    endfunction
    
    virtual task apply_error_condition();
        set_dsi_uv_for_channel(channel, 1);
        #7ms;
    endtask
    
    virtual task release_error_condition();
        project_pkg::dsi_logic_t	expected_value = '1;
        expected_value = expected_value ^ project_pkg::dsi_logic_t'(1<<channel);
        registers.check_flag(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, expected_value);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, '0);
        registers.check_flag(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, '0);
        set_dsi_uv_for_channel(channel, 0);
        #7ms;
    endtask
    
    virtual task run_tests();
        error_name = $sformatf("%s_%1d", error_name, channel);
        irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DSIUV;
        super.run_tests();
    endtask
    
endclass

class hardware_error_undervoltage_dsi_with_deactivated_channels_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_undervoltage_dsi_with_deactivated_channels_seq)
    
    function new(string name = "");
        super.new("hardware_error_undervoltage_dsi_with_deactivated_channels");
        error_name = "UNDERVOLTAGE_DSI with deactivated channels";
        status_type = IRQ;
    endfunction
    
    virtual task apply_error_condition();
        check_dsi_voltages('1);
        set_dsi_uv_for_channel(channel, 1);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, (1<<channel));
        #50us;
        check_dsi_voltages(1<<channel);
        #(7ms-50us);
    endtask
    
    virtual task release_error_condition();
        project_pkg::dsi_logic_t	expected_value = '1;
        expected_value = expected_value ^ project_pkg::dsi_logic_t'(1<<channel);
        check_dsi_voltages('0);
        registers.check_flag(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, 0);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, '1);
        registers.check_flag(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, expected_value);
        #50us;
        check_dsi_voltages(expected_value);
        set_dsi_uv_for_channel(channel, 0);
        #7ms;
    endtask
    
    virtual task run_tests();
        error_name = $sformatf("%s_%1d", error_name, channel);
        irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DSIUV;
        super.run_tests();
    endtask
    
endclass

class hardware_error_overvoltage_dsi_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_overvoltage_dsi_seq)
    
    function new(string name = "");
        super.new("hardware_error_overvoltage_dsi");
        error_name = "OVERVOLTAGE_DSI";
        status_type = IRQ;
    endfunction
    
    virtual task apply_error_condition();
        set_dsi_ov_for_channel(channel, 1);
        #7ms;
    endtask
    
    virtual task release_error_condition();
        set_dsi_ov_for_channel(channel, 0);
        #7ms;
    endtask
    
    virtual task run_tests();
        error_name = $sformatf("%s_%1d", error_name, channel);
        irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DSIOV;
        super.run_tests();
    endtask
    
endclass

class hardware_error_overvoltage_dsi_with_deactivated_channels_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_overvoltage_dsi_with_deactivated_channels_seq)
    
    function new(string name = "");
        super.new("hardware_error_overvoltage_dsi_with_deactivated_channels");
        error_name = "OVERVOLTAGE_DSI with deactivated channels";
        status_type = IRQ;
    endfunction
    
    virtual task apply_error_condition();
        set_dsi_ov_for_channel(channel, 1);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, (1<<channel));
        #50us;
        check_dsi_voltages(1<<channel);
        #(7ms-50us);
    endtask
    
    virtual task release_error_condition();
        project_pkg::dsi_logic_t	expected_value = '1;
        expected_value = expected_value ^ project_pkg::dsi_logic_t'(1<<channel);
        check_dsi_voltages('0);
        registers.check_flag(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, 0);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, '1);
        registers.check_flag(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, expected_value);
        #50us;
        check_dsi_voltages(expected_value);
        set_dsi_ov_for_channel(channel, 0);
        #7ms;
    endtask
    
    virtual task run_tests();
        error_name = $sformatf("%s_%1d", error_name, channel);
        irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DSIOV;
        super.run_tests();
    endtask
    
endclass

class hardware_error_hw_fail_dsi_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_hw_fail_dsi_seq)
    
    function new(string name = "");
        super.new("hardware_error_hw_fail_dsi");
        error_name = "HW_FAIL_DSI";
        status_type = IRQ;
    endfunction
    
    virtual task apply_error_condition();
        hdl_force($sformatf(`STRING_OF(`DSI_STATE_PATH), channel), 'h1F);
    endtask
    
    virtual task release_error_condition();
        hdl_release($sformatf(`STRING_OF(`DSI_STATE_PATH), channel));
    endtask
    
    virtual task run_tests();
        error_name = $sformatf("%s_%1d", error_name, channel);
        irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL;
        super.run_tests();
    endtask
endclass

class hardware_error_hw_fail_dsi_iload_seq extends hardware_error_seq;
	`uvm_object_utils(hardware_error_hw_fail_dsi_iload_seq)
	
	function new(string name = "");
		super.new("hardware_error_hw_fail_dsi_iload");
		error_name = "HW_FAIL_DSI_ILOAD";
		status_type = IRQ;
	endfunction
	
	virtual task apply_error_condition();
		hdl_force($sformatf(`STRING_OF(`DSI_ILOAD_STATE_PATH), channel), 'b11);
	endtask
	
	virtual task release_error_condition();
		hdl_release($sformatf(`STRING_OF(`DSI_ILOAD_STATE_PATH), channel));
	endtask
	
	virtual task run_tests();
		error_name = $sformatf("%s_%1d", error_name, channel);
		irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL;
		super.run_tests();
	endtask
endclass

class hardware_error_hw_fail_dsi_core_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_hw_fail_dsi_core_seq)
    
    function new(string name = "");
        super.new("hardware_error_hw_fail_dsi_core");
        error_name = "HW_FAIL_DSI_CORE";
        status_type = IRQ;
    endfunction
    
    virtual task apply_error_condition();
        hdl_force($sformatf(`STRING_OF(`DSI_CORE_STATE_PATH), channel), 'hF);
    endtask
    
    virtual task release_error_condition();
        hdl_release($sformatf(`STRING_OF(`DSI_CORE_STATE_PATH), channel));
    endtask
    
    virtual task run_tests();
        error_name = $sformatf("%s_%1d", error_name, channel);
        irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL;
        super.run_tests();
    endtask
    
endclass


class hardware_error_hw_fail_dsi3_command_buffer_wrong_command_seq extends hardware_error_seq;
    
    rand logic[15:0] wrong_command;
    
    `uvm_object_utils(hardware_error_hw_fail_dsi3_command_buffer_wrong_command_seq)
    
    function new(string name = "");
        super.new("hardware_error_hw_fail_dsi3_command_buffer_wrong_command");
        error_name = "HW_FAIL_DSI_COMMAND_BUFFER";
        status_type = IRQ;
		enable_sim_log = 1'b0;
    endfunction
    
    virtual task run_tests();
        error_name = $sformatf("%s_%1d", error_name, channel);
        irq_field = regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL;
        super.run_tests();	
    endtask
    
    virtual task apply_error_condition();
        uvm_reg_data_t buffer_address;
        
        `uvm_info(get_type_name(), $sformatf("implant wrong command 0x%4h into DSI command buffer at channel %0d", wrong_command, channel), UVM_MEDIUM)
        #10us;
        
        // FIXME: upload a TDMA scheme (otherwise start PDCM will not work)
        `spi_frame_begin
        `spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01 << channel; wait_time == 15'd50;)
        `spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        regmodel.DSI_CMD_STAT[channel].ring_buffer_registers.BUF_READ_POINTER.read(status, buffer_address);
        // change command in RAM
        jtag_write(int'(buffer_address), int'(wrong_command));
    endtask
    
    virtual task release_error_condition();
        // nothing to do here
    endtask
    
endclass


class hardware_error_undervoltage_vcc_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_undervoltage_vcc_seq)
    
    function new(string name = "");
        super.new("hardware_error_undervoltage_vcc");
        error_name = "UNDERVOLTAGE_VCC";
    endfunction	
    
    virtual task run_tests();
        irq_field = regmodel.Supply.supply_registers.SUP_IRQ_STAT.VCCUV;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        set_vcc_uv(1'b1);
    endtask
    
    virtual task release_error_condition();
        set_vcc_uv(1'b0);
    endtask
    
endclass

class hardware_error_undervoltage_cldo_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_undervoltage_cldo_seq)
    
    function new(string name = "");
        super.new("hardware_error_undervoltage_cldo");
        error_name = "UNDERVOLTAGE_CLDO";
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.Supply.supply_registers.SUP_IRQ_STAT.LDOUV;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        set_cldo_uv(1'b1);
    endtask
    
    virtual task release_error_condition();
        set_cldo_uv(1'b0);
    endtask
    
endclass

class hardware_error_ref_fail_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_ref_fail_seq)
    
    function new(string name = "");
        super.new("hardware_error_ref_fail");
        error_name = "REF_FAIL";
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.Supply.supply_registers.SUP_IRQ_STAT.REF_FAIL;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        set_ref_fail(1'b1);
    endtask
    
    virtual task release_error_condition();
        set_ref_fail(1'b0);
    endtask
    
endclass

class hardware_error_hw_fail_spi_seq extends hardware_error_seq;
    `uvm_object_utils(hardware_error_hw_fail_spi_seq)
    
    function new(string name = "");
        super.new("hardware_error_hw_fail_spi");
        error_name = "HW_FAIL_SPI";
        status_type = IRQ;
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.SPI.SPI_registers.SPI_IRQ_STAT.HW_FAIL;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        #1us;
        hdl_force(`STRING_OF(`SPI_STATE_PATH), 'hF);
        #10us;
        // release it to be able to send SPI commands
        hdl_release(`STRING_OF(`SPI_STATE_PATH));
        #1us;
        `spi_frame_begin
        `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
//        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1'b1);
    endtask
    
    virtual task release_error_condition();
        // nothing to do here
    endtask
endclass

class hardware_error_hw_fail_main_seq extends hardware_error_seq;
    randc logic[3:0]	fsm_state;
    
    constraint co_fsm_state {fsm_state inside {[4'he:4'hf]};}
    
    `uvm_object_utils(hardware_error_hw_fail_main_seq)
    
    function new(string name = "");
        super.new("hardware_error_hw_fail_main");
        error_name = "HW_FAIL_MAIN";
        status_type = IRQ;
		enable_sim_log = 1'b0;
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.HW_FAIL;
        super.run_tests();
    endtask
    
    
    virtual task apply_error_condition();
        hdl_force(`STRING_OF(`MAIN_STATE_PATH), fsm_state);
    endtask
    
    virtual task release_error_condition();
        hdl_release(`STRING_OF(`MAIN_STATE_PATH));
        #500us;
    endtask
endclass

class hardware_error_hw_fail_command_control_seq extends hardware_error_seq;
    randc logic[3:0]	fsm_state;
    
    constraint co_fsm_state {fsm_state inside {[4'hb:4'hf]};}
    
    `uvm_object_utils(hardware_error_hw_fail_command_control_seq)
    
    function new(string name = "");
        super.new("hardware_error_hw_fail_command_control");
        error_name = "HW_FAIL_COMMAND_CONTROL";
        status_type = IRQ;
		enable_sim_log = 1'b0;
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.HW_FAIL;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        #10us;
        hdl_force(`STRING_OF(`COMMAND_CONTROL_STATE_PATH), fsm_state);
        #0.1us;
        // release it to be able to do anything
        hdl_release(`STRING_OF(`COMMAND_CONTROL_STATE_PATH));
        #2us;
        `spi_frame_begin
        `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
        // do dummy access
        begin
            `spi_frame_begin
            `spi_frame_create(spi_read_status_seq,)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
            `spi_frame_end
        end
    endtask
    
    virtual task release_error_condition();
        // nothing to do here
    endtask
    
endclass

class hardware_error_hw_fail_command_control_wrong_command_seq extends hardware_error_seq;
    
    rand logic[3:0]	wrong_command;
    rand logic[3:0]	initial_command;
    
    constraint co_initial_command {initial_command inside {CMD_PDCM, CMD_DSI_WAIT};}
    constraint co_initial_type_wait   {wrong_command == CMD_DSI_WAIT -> initial_command == CMD_PDCM;}
	constraint co_initial_type_upload {wrong_command == CMD_UPLOAD_TDMA -> initial_command == CMD_PDCM;}
    
    `uvm_object_utils(hardware_error_hw_fail_command_control_wrong_command_seq)
    
    function new(string name = "");
        super.new("hardware_error_hw_fail_command_control_wrong_command");
        error_name = "HW_FAIL_COMMAND_CONTROL";
        status_type = IRQ;
		enable_sim_log = 1'b0;
    endfunction
    
    virtual task run_tests();
        irq_field = regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.HW_FAIL;
        super.run_tests();
    endtask
    
    virtual task apply_error_condition();
        spi_read_master_register_seq read_seq;
        spi_pdcm_seq pdcm_seq;
        spi_dsi_wait_seq dsi_wait_seq;
        spi_dsi_command_seq cmd_seq;
        logic[15:0] buffer_address;
        spi_tx_crc_request_seq tx_crc;
        spi_tr  spi_transaction;
        int spi_word;
        logic[15:0] crc_data_in[$];
        
        `uvm_info(get_type_name(), $sformatf("implant wrong command 0x%4h into SPI command buffer", {wrong_command, 12'hC00}), UVM_MEDIUM)
        
        #10us;
        
        `uvm_do_on_with(spi_transaction, m_spi_agent.m_sequencer, {tr_type == SPI_START;})
        
        `uvm_create(read_seq)
        read_seq.address = 12'(ADDR_SPI_CMD_STAT_BUF_READ_POINTER);
        for (spi_word = 0; spi_word < read_seq.get_word_count(); spi_word++) begin
            crc_data_in.push_back(read_seq.get_word(spi_word));
            send_spi_transaction(read_seq.get_word(spi_word), spi_word, spi_transaction);
        end
        
        `uvm_create(pdcm_seq)
        `uvm_create(dsi_wait_seq)
        if(pdcm_seq.randomize() != 1) `uvm_error(this.get_name(), "randomization failed")
        if(dsi_wait_seq.randomize() != 1) `uvm_error(this.get_name(), "randomization failed")
        cmd_seq = (initial_command == CMD_PDCM) ? pdcm_seq : dsi_wait_seq;
        for (spi_word = 0; spi_word < cmd_seq.get_word_count(); spi_word++) begin
            crc_data_in.push_back(cmd_seq.get_word(spi_word));
            send_spi_transaction(cmd_seq.get_word(spi_word), spi_word, spi_transaction);
            if(spi_word == 0) begin
                // READ_POINTER content is available.
                buffer_address = spi_transaction.data_out;
                `uvm_info(get_type_name(), $sformatf("buffer_address 0x%h", buffer_address), UVM_MEDIUM)
            end
        end
        
        // change command in RAM
        jtag_write(int'(buffer_address), int'({wrong_command, 12'hC00}));
        
        // validate SPI command
        `uvm_create_on(tx_crc, m_spi_agent.m_sequencer)
        void'(tx_crc.randomize() with {mosi_crc_correct == 1'b1;});
        crc_data_in.push_back(tx_crc.get_word(0));
        tx_crc.mosi_crc = crc_calculation_pkg::spi_calculate_crc(1'b1, crc_data_in);
        `uvm_send(tx_crc)
        `uvm_do_on_with(spi_transaction, m_spi_agent.m_sequencer, {tr_type == SPI_END;})
        #10us;
        `spi_frame_begin
        `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
    endtask
    
    virtual task send_spi_transaction(logic[15:0] word, int word_index, ref spi_tr spi_transaction);
        `uvm_create_on (spi_transaction, m_spi_agent.m_sequencer)
        spi_transaction.tr_type = spi_pkg::SPI_DATA;
        spi_transaction.data_in = word;
        spi_transaction.bit_count = 16;
        spi_transaction.word_index = word_index;
        spi_transaction.set_name("spi-data");
        `uvm_send (spi_transaction)     
    endtask
    
    virtual task release_error_condition();
        // nothing to do here
    endtask
    
endclass

