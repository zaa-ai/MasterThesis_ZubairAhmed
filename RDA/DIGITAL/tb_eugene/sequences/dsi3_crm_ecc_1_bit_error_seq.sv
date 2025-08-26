class dsi3_crm_ecc_1_bit_error_seq extends base_dsi_master_seq;
    
    `uvm_object_utils(dsi3_crm_ecc_1_bit_error_seq)
    
    error_t	bit_error;
    
    function new(string name = "");
        super.new("dsi3_crm_ecc_1_bit_error");
        bit_error = ONE_BIT_ERR;
    endfunction
    
    virtual task run_tests();
		log_sim_description("Testcase for single bit ECC failures", LOG_LEVEL_TOP);
        clear_all_irqs();
		#20us;
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            `create_and_send_with(ecc_dsi3_crm_data_buffer_fsm_seq,           channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_crm_data_buffer_read_pointer_seq,  channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_crm_data_buffer_write_pointer_seq, channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_crm_data_buffer_valid_pointer_seq, channel == local::channel; bit_error == local::bit_error; )
            
            `create_and_send_with(ecc_dsi3_pdcm_data_buffer_fsm_seq,           channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_pdcm_data_buffer_read_pointer_seq,  channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_pdcm_data_buffer_write_pointer_seq, channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_pdcm_data_buffer_valid_pointer_seq, channel == local::channel; bit_error == local::bit_error; )
            
            `create_and_send_with(ecc_dsi3_command_buffer_fsm_seq,           channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_command_buffer_read_pointer_seq,  channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_command_buffer_write_pointer_seq, channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_command_buffer_valid_pointer_seq, channel == local::channel; bit_error == local::bit_error; )
            
            `create_and_send_with(ecc_dsi3_tdma_buffer_state_seq,                 channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_buffer_packet_index_seq,          channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_packet_counter_seq,               channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_state_seq,                        channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_state2branch_seq,                 channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_writer_packet_index_seq,          channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_header_count_seq,            channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_header_period_seq,           channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_next_packet_info_seq,        channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_next_packet_earliest_seq,    channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_next_packet_latest_seq,      channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_current_packet_info_seq,     channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_current_packet_earliest_seq, channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_tdma_info_current_packet_latest_seq,   channel == local::channel; bit_error == local::bit_error; )

            
            // ECC RAM -> dsi command 
            for (int ecc_error_position=0; ecc_error_position<project_pkg::ECC_WIDTH; ecc_error_position++) begin
                `create_and_send_with(ecc_dsi3_command_reading_jtag_ecc_inject_error_seq, channel == local::channel; bit_error == local::bit_error; bit_position == local::ecc_error_position; )
            end
            
            // ECC receiver -> RAM
            `create_and_send_with(ecc_dsi3_receiver_pdcm_to_ram_error_seq, channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_receiver_crm_to_ram_error_seq, channel == local::channel; bit_error == local::bit_error; )
            
            // ECC DSI3 receive data
            `create_and_send_with(ecc_dsi3_receiver_rx_data_error_seq, channel == local::channel; bit_error == local::bit_error; )
            `create_and_send_with(ecc_dsi3_receiver_rx_data_error_while_idle_seq, channel == local::channel; bit_error == local::bit_error; )
            
            `create_and_send_with(ecc_dsi3_transmit_data_error_seq, channel == local::channel; bit_error == local::bit_error; )
            
            for (int i = 0; i < 3; i++) begin
                `create_and_send_with(ecc_dsi3_data_high_error_seq, channel == local::channel; bit_error == local::bit_error; errorInjectionTime == local::i;)
                `create_and_send_with(ecc_dsi3_data_low_error_seq,  channel == local::channel; bit_error == local::bit_error; errorInjectionTime == local::i;)
            end
            
        end
        `create_and_send_with(ecc_spi_command_buffer_fsm_seq,           bit_error == local::bit_error; )
        `create_and_send_with(ecc_spi_command_buffer_read_pointer_seq,  bit_error == local::bit_error; )
        `create_and_send_with(ecc_spi_command_buffer_write_pointer_seq, bit_error == local::bit_error; )
        `create_and_send_with(ecc_spi_command_buffer_valid_pointer_seq, bit_error == local::bit_error; )
        
        //FIXME:
        // ECC SPI -> RAM
        
        // ECC RAM -> command control
        for (int i = 0; i < 2; i++) begin
            `create_and_send_with(ecc_command_control_error_command_counter_seq, bit_error == local::bit_error; whileCmdsPresent == local::i[0];)
            `create_and_send_with(ecc_command_control_error_channels_seq, bit_error == local::bit_error; whileCmdsPresent == local::i[0];)
        end
        
        `create_and_send_with(ecc_command_control_error_seq, bit_error == local::bit_error; )
        for (int ecc_error_position=0; ecc_error_position<project_pkg::ECC_WIDTH; ecc_error_position++) begin
            `create_and_send_with(ecc_command_control_error_jtag_ecc_inject_seq, bit_error == local::bit_error; bit_position == local::ecc_error_position; )
        end
        `create_and_send_with(ecc_command_control_error_jtag_ecc_sel_val_seq, bit_error == local::bit_error;)
        if (bit_error == TWO_BIT_ERR) begin
            `create_and_send_with(ecc_command_control_error_jtag_ecc_swap_seq,    bit_error == local::bit_error;)
        end
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            `create_and_send_with(ecc_spi_read_dsi3_crm_data_error_seq,    channel == local::channel;	bit_error == local::bit_error;)
        end
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            `create_and_send_with(ecc_spi_read_dsi3_pdcm_data_error_seq,    channel == local::channel;   bit_error == local::bit_error;)
        end
        repeat(3)
            `create_and_send_with(ecc_spi_received_data_error_seq, bit_error == local::bit_error;)
        
        repeat(3)
            `create_and_send_with(ecc_spi_read_ram_data_error_with_forcing_at_fifo_seq,    bit_error == local::bit_error;)
        repeat(3)
            `create_and_send_with(ecc_spi_read_ram_data_error_with_forcing_at_fifo_read_seq,    bit_error == local::bit_error;)
        repeat(3)
            `create_and_send_with(ecc_spi_read_ram_data_error_seq,    bit_error == local::bit_error;)
        repeat(3)
            `create_and_send_with(ecc_spi_read_ram_data_error_with_forcing_at_crc_seq,    bit_error == local::bit_error;)
        repeat(3)
            `create_and_send_with(ecc_spi_read_ram_data_error_with_forcing_at_shift_in_seq,    bit_error == local::bit_error;)
        repeat(3)
            `create_and_send_with(ecc_spi_read_ram_data_error_with_forcing_at_shift_out_seq,    bit_error == local::bit_error;)
    endtask
    
endclass
