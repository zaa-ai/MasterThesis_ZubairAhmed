class ecc_error_base_seq extends base_dsi_master_seq;
    // SPI
    parameter string PATH_SPI_TX_FIFO_DATA					= {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_tx_fifo.i_fifo_data"};
    parameter string PATH_SPI_TX_FIFO_DAA_DATA				= {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_tx_fifo.i_fifo_data.data"};
    parameter string PATH_SPI_TX_FIFO_DOUT_DATA             = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_tx_fifo.tx_fifo[0]"};
    parameter string PATH_SPI_CORE_CRC_DATA                 = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_core.crc_out_for_miso"};
    parameter string PATH_SPI_CORE_SHIFT_IN_DATA            = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_core.shift_in[0]"};
    parameter string PATH_SPI_CORE_IC_STATUS_DATA           = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_core.i_status_word"};
    parameter string PATH_SPI_CORE_SHIFT_OUT_DATA           = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_core.shift_out"};
    parameter string PATH_SPI_CORE_DATA_RECEIVED            = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_spi.i_spi_sync.o_rx_data.data"};
    
    // RAM
    parameter string PATH_RAM_DATA_READ_ECC					= { `STRING_OF( `LOGIC_TOP_PATH ), ".i_data_storage.i_ram_wrapper_ecc_with_bist.elip.data_read.ecc"};
    parameter string PATH_RAM_DATA_READ_DATA				= { `STRING_OF( `LOGIC_TOP_PATH ), ".i_data_storage.i_ram_wrapper_ecc_with_bist.elip.data_read.data"};
    
    // DSI3
    parameter string PATH_DSI3_RECEIVER_PDCM_TO_RAM = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.pdcm_data_writer"};
    parameter string PATH_DSI3_RECEIVER_CRM_TO_RAM = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.crm_data_writer"};
    parameter string PATH_DSI3_RECEIVER_RX_DATA = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.general_data_writer_inputs.rx_data"};
    parameter string PATH_DSI3_TRANSMIT_DATA = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_dsi3_core.i_dsi3_transmit.i_data_ecc_register.data_reg"};
    parameter string PATH_DSI3_CORE_DATA_LOW = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.data_low.data"};
    parameter string PATH_DSI3_CORE_DATA_HIGH = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.data_high.data"};
   
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_BUFFER_STATE                 = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.u_tdma_buffer.i_ecc_register_state.data_reg"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_BUFFER_PACKET_INDEX          = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.u_tdma_buffer.i_packet_index_ecc_register.data_reg"};
    parameter string PATH_DSI3_TDMA_MANAGER_PACKET_COUNTER                    = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.i_ecc_register_packet_counter.data_reg"};
    parameter string PATH_DSI3_TDMA_MANAGER_STATE                             = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.i_ecc_register_fsm_state.data_reg"};
    parameter string PATH_DSI3_TDMA_MANAGER_STATE2BRANCH                      = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.i_ecc_register_fsm_state_to_branch.data_reg"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_HEADER_COUNT            = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.header.packet_count.packet_count"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_HEADER_PERIOD           = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.header.period.data"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_NEXT_PACKET_INFO        = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.next_packet.earliest.data"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_NEXT_PACKET_EARLIEST    = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.next_packet.latest.data"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_NEXT_PACKET_LATEST      = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.next_packet.info.data"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_CURRENT_PACKET_INFO     = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.current_packet.earliest.data"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_CURRENT_PACKET_EARLIEST = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.current_packet.latest.data"};
    parameter string PATH_DSI3_TDMA_MANAGER_TDMA_INFO_CURRENT_PACKET_LATEST   = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.i_tdma_manager.tdma_info_ecc.current_packet.earliest.data"};
    parameter string PATH_DSI3_TDMA_MANAGER_WRITER_PACKET_INDEX               = { `STRING_OF( `LOGIC_TOP_PATH ), ".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.tdma_header.packet_count.packet_count"};
    
    // COMMAND_CONTROL
    parameter string PATH_COMMAND_CONTROL_CHANNELS        = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_command_control.i_channels_ecc_register.data_reg"};
    parameter string PATH_COMMAND_CONTROL_COMMAND_COUNTER = {`STRING_OF( `LOGIC_TOP_PATH ), ".i_command_control.i_command_counter_ecc_register.data_reg"};
    
    parameter string PATH_BUFFERS = "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_buffers";
    // FSM + pointer ECC
    parameter string PATH_SPI_COMMAND_BUFFER_FSM_STATE		= {PATH_BUFFERS, ".i_command_buffer.i_state_fsm_ecc_register.data_reg"};
    parameter string PATH_SPI_COMMAND_BUFFER_READ_POINTER	= {PATH_BUFFERS, ".i_command_buffer.i_read_ecc_register.data_reg"};
    parameter string PATH_SPI_COMMAND_BUFFER_VALID_POINTER	= {PATH_BUFFERS, ".i_command_buffer.i_valid_ecc_register.data_reg"};
    parameter string PATH_SPI_COMMAND_BUFFER_WRITE_POINTER	= {PATH_BUFFERS, ".i_command_buffer.i_write_ecc_register.data_reg"};
    parameter string PATH_DSI3_COMMAND_BUFFER_FSM_STATE		= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_command_buffer.i_state_fsm_ecc_register.data_reg"};
    parameter string PATH_DSI3_COMMAND_BUFFER_READ_POINTER	= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_command_buffer.i_read_ecc_register.data_reg"};
    parameter string PATH_DSI3_COMMAND_BUFFER_VALID_POINTER	= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_command_buffer.i_valid_ecc_register.data_reg"};
    parameter string PATH_DSI3_COMMAND_BUFFER_WRITE_POINTER	= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_command_buffer.i_write_ecc_register.data_reg"};
    parameter string PATH_DSI3_CRM_DATA_BUFFER_FSM_STATE		= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_crm_data_buffer.i_state_fsm_ecc_register.data_reg"};
    parameter string PATH_DSI3_CRM_DATA_BUFFER_READ_POINTER		= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_crm_data_buffer.i_read_ecc_register.data_reg"};
    parameter string PATH_DSI3_CRM_DATA_BUFFER_VALID_POINTER	= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_crm_data_buffer.i_valid_ecc_register.data_reg"};
    parameter string PATH_DSI3_CRM_DATA_BUFFER_WRITE_POINTER	= {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_crm_data_buffer.i_write_ecc_register.data_reg"};
    parameter string PATH_DSI3_PDCM_DATA_BUFFER_FSM_STATE        = {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_pdcm_data_buffer.i_state_fsm_ecc_register.data_reg"};
    parameter string PATH_DSI3_PDCM_DATA_BUFFER_READ_POINTER     = {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_pdcm_data_buffer.i_read_ecc_register.data_reg"};
    parameter string PATH_DSI3_PDCM_DATA_BUFFER_VALID_POINTER    = {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_pdcm_data_buffer.i_valid_ecc_register.data_reg"};
    parameter string PATH_DSI3_PDCM_DATA_BUFFER_WRITE_POINTER    = {PATH_BUFFERS, ".generate_dsi_buffers[%1d].i_dsi3_pdcm_data_buffer.i_write_ecc_register.data_reg"};
    
    rand int unsigned channel;
    
    constraint co_channel {channel < project_pkg::DSI_CHANNELS;}
    rand error_t bit_error;
    
    // to be initialized in sub-sequences!
    uvm_reg_field	irq_stat_ecc_field;
    uvm_reg_field	irq_stat_ecc_corr_field;
    string path;
    string test;
    protected	bit	is_single_channel;
    protected	bit	issues_only_double_error;
    
    `uvm_object_utils(ecc_error_base_seq)
    
    function new(string name = "");
        super.new(name);
        is_single_channel = 1'b0;
        issues_only_double_error = 1'b0;
    endfunction
    
    virtual task run_tests();
        initialize();
        if(bit_error == TWO_BIT_ERR) begin
            get_checker_config().disable_all_master_transmission_checkers();
        end
        if (is_single_channel == 1'b1)
            log_sim_description($sformatf("%s in %s", get_error_type_name(bit_error), test), LOG_LEVEL_OTHERS);
        else 
            log_sim_description($sformatf("%s in %s at channel %0d", get_error_type_name(bit_error), test, channel), LOG_LEVEL_OTHERS);
        if (check_sequence_parameters()) begin
            setup();
            run_check();
            run_check_after_error();
            tear_down();
        end
    endtask
    
    virtual task run_check();
        fork
            begin
                apply_stimuli();
            end
            begin
                apply_error();
                #5us;
                check_and_clear_ecc_irq(get_field_mask());
            end
        join
    endtask
    
    virtual function bit check_sequence_parameters();
        bit result = 1'b1;
        if (path == "") begin
            `uvm_error(this.get_type_name(), "path is not set in sub-sequence")
            result &= 1'b0;
        end
        if (test == "") begin
            `uvm_error(this.get_type_name(), "test is not set in sub-sequence")
            result &= 1'b0;
        end
        if (irq_stat_ecc_field == null) begin
            `uvm_error(this.get_type_name(), "corresponding ECC IRQ register is not set")
            result &= 1'b0;
        end
        if (irq_stat_ecc_corr_field == null) begin
            `uvm_error(this.get_type_name(), "corresponding ECC CORR IRQ register is not set")
            result &= 1'b0;
        end
        return result;
    endfunction
    
    virtual task setup();
        enable_all_interrupt_sources();
        clear_all_irq();
        check_HE_ic_status(1'b0);
        check_intb(1'b1);
    endtask
    
    virtual task tear_down();
        clear_slave_crm_scheme_fifos();
    endtask
    
    virtual function void initialize();
        
        `uvm_fatal(this.get_type_name(), $sformatf("%s should not be used. Use only extended classes of this class!", get_type_name()))
    endfunction
    
    virtual function int get_field_mask();
        int mask;
        if (is_single_channel == 1'b1)
            mask = 1 << (irq_stat_ecc_field.get_lsb_pos());
        else
            mask = 1 << (irq_stat_ecc_field.get_lsb_pos() + channel);
        $display("mask=%4h", mask);
        return mask;
    endfunction
    
    virtual function bit get_intb_value();
        return 1'b0;
    endfunction
    
    virtual function int get_expected_irq();
        return (bit_error == TWO_BIT_ERR) ? ((issues_only_double_error) ? 'h0400 : 'h0c00) : 'h0800;
    endfunction
    
    virtual task apply_stimuli();
        bit all_channels_correct = (bit_error != TWO_BIT_ERR) ? 1'b1 : 1'b0;
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == local::all_channels_correct; bad_channel == local::channel; )
    endtask
    
    virtual task apply_error();
    endtask
    
    virtual task apply_ecc_failure();
    endtask
    
    virtual task run_check_after_error();
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1; )
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
    //#####   tasks for all   #####
    virtual task check_and_clear_ecc_irq(int exp_value);
        bit intb_value = get_intb_value();
        int expected_irq = get_expected_irq();
        check_intb(intb_value);
        
        `uvm_info(this.get_type_name(), $sformatf("bit_error = %s", bit_error.name), UVM_INFO)
        
        case(bit_error)
            NO_BIT_ERR: begin
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT, 0);
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT, 0);
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT, 0);
            end
            ONE_BIT_ERR: begin
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT, exp_value);
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT, 0);
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT, expected_irq);
                registers.write_and_check_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_MASK, '0);
                check_intb(intb_value);
                registers.write_and_check_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_MASK, 64'h0000_0000_0000_f333);
                check_intb(intb_value);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_MASK, exp_value);
                check_intb(1'b1);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_MASK, exp_value);
                check_intb(intb_value);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK, expected_irq);
                check_intb(1'b1);
            end
            TWO_BIT_ERR: begin
                int expected_value_correction = (issues_only_double_error) ? 0 : exp_value;
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT, expected_value_correction);
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT, exp_value);
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT, expected_irq);
                check_intb(intb_value);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_MASK, expected_value_correction);
                check_intb(intb_value);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_MASK, exp_value);
                check_intb(1'b1);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_MASK, expected_value_correction);
                if (issues_only_double_error)	check_intb(1'b1);
                else							check_intb(intb_value);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_MASK, exp_value);
                check_intb(intb_value);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK, expected_irq);
                check_intb(1'b1);
                invert_irq_mask_value(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK, expected_irq);
                check_intb(intb_value);
            end
        endcase
        
        clear_all_irq();
        check_intb(1'b1);
    endtask
    
    virtual task invert_irq_mask_value(uvm_reg register, shortint unsigned mask);
        uvm_reg_data_t	read_value;
        register.read(status, read_value);
        read_value = read_value ^ uvm_reg_data_t'(mask);
        registers.write_and_check_register(register, read_value);
    endtask
    
    virtual task write_and_check_irq_register(uvm_reg register, shortint write_value, shortint expected_read_value);
        register.write(status, write_value);
        registers.check_register(register, expected_read_value);
    endtask
    
    virtual task clear_all_irq();
        // clear all flag in register ECC_CORR_IRQ_STAT
        write_and_check_irq_register(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT, 16'hFFFF, 16'h0000);
        
        // clear all flag in register ECC_IRQ_STAT
        write_and_check_irq_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT, 16'hFFFF, 16'h0000);
        
        // clear all flag in register IRQ_STAT
        write_and_check_irq_register(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT, 16'hFFFF, 16'h0000);
    endtask
    
    task check_HE_ic_status(bit expected_he_flag);
        spi_read_status_seq status_seq;	
        `spi_frame_begin
        `spi_frame_send(status_seq,)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        if(status_seq.status.get_value(HE) != expected_he_flag) `uvm_error(this.get_type_name(), $sformatf("Unexpected HE flag in IC status word, expected %b, got %b", expected_he_flag, status_seq.status.get_value(HE)))
    endtask
    
    virtual task enable_all_interrupt_sources();
        registers.write_and_check_register(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK, 16'h1E7f);
        registers.write_and_check_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_MASK, 16'hf3FF);
        registers.write_and_check_register(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_MASK, 16'hf3FF);
    endtask
    
    virtual function string get_error_type_name(error_t	bit_error);
        case (bit_error)
            ONE_BIT_ERR: return "single bit error";
            TWO_BIT_ERR: return "double bit error";
            default: return "no bit error";
        endcase
    endfunction
    
endclass
