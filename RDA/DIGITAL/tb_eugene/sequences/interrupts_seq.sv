class interrupts_seq extends base_dsi_master_seq;
    
    `uvm_object_utils(interrupts_seq)
    
    function new(string name = "");
        super.new("interrupts");
    endfunction : new
    
    virtual task run_tests();
        log_sim_description("Testcase for all interrupts and masks", LOG_LEVEL_TOP);
        
        // global IRQs
        `create_and_send(otp_fail_irq_seq)
        `create_and_send(reset_irq_seq)
        `create_and_send(clkref_irq_seq)
        `ifndef GATE_LEVEL
        `create_and_send(hw_fail_irq_seq)
        `endif
        
        // supply IRQs
        `create_and_send(supply_ref_fail_irq_seq)
        `create_and_send(supply_vccuv_irq_seq)
        `create_and_send(supply_ldouv_irq_seq)
        `create_and_send(supply_otw_irq_seq)
        `create_and_send(supply_ote_irq_seq)
        
        // channel based IRQs
        for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
            // buffer IRQs
            `create_and_send_with(buf_dsi_cmd_fe_irq_seq, channel == i; channel_based == 1'b1;)
            `create_and_send_with(buf_dsi_pdcm_data_fe_irq_seq, channel == i; channel_based == 1'b1;)
            `create_and_send_with(buf_dsi_crm_data_fe_irq_seq, channel == i; channel_based == 1'b1;)
            
            // DSI IRQs
            `create_and_send_with(dsi_com_err_irq_seq, channel == i; channel_based == 1'b1;)
            `create_and_send_with(dsi_dsiov_irq_seq, channel == i; channel_based == 1'b1;)
            `create_and_send_with(dsi_dsiuv_irq_seq, channel == i; channel_based == 1'b1;)
            `create_and_send_with(dsi_dmof_irq_seq, channel == i; channel_based == 1'b1;)
            `create_and_send_with(dsi_sync_err_irq_seq, channel == i; channel_based == 1'b1;)
            `ifndef GATE_LEVEL
            `create_and_send_with(dsi_hw_fail_irq_seq, channel == i; channel_based == 1'b1;)
            `endif
            `create_and_send_with(dsi_iq_err_irq_seq, channel == i; channel_based == 1'b1;)
        end
        
        // SPI IRQs
        `create_and_send(buf_spi_cmd_fe_irq_seq)
        `create_and_send(spi_cmd_inc_irq_seq)
        `create_and_send(spi_crc_err_irq_seq)
        `create_and_send(spi_ali_err_irq_seq)
        `create_and_send(spi_cmd_ign_irq_seq)
        `ifndef GATE_LEVEL
        `create_and_send(spi_hw_fail_irq_seq)
        `endif
        
        #3ms;
    endtask
    
endclass
