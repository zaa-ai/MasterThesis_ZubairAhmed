/*------------------------------------------------------------------------------
 * File          : dsi_com_err_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class dsi_com_err_irq_seq extends dsi_base_irq_seq;
    
    `uvm_object_utils(dsi_com_err_irq_seq) 
    
    function new(string name = "DSI.COM_ERR");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.COM_ERR;
    endfunction
    
    task apply_interrupt_condition();
        // invalidate any existing TDMA scheme
        `spi_frame_begin
            `spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #1us;
        
        transaction_recorder.enable_recorder();
        `spi_frame_begin
            `spi_frame_create(spi_pdcm_seq, channel_bits == (2'b01 << channel);)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #100us;
        
        transaction_recorder.expect_tr_count_for_all_channels(0);
        
        #10us;
    endtask
    
    task release_interrupt_condition();
        
    endtask
endclass