/*------------------------------------------------------------------------------
 * File          : dsi_sync_err_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class dsi_sync_err_irq_seq extends dsi_base_irq_seq;
    
    `uvm_object_utils(dsi_sync_err_irq_seq) 
    
    function new(string name = "DSI.SYNC_ERR");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.SYNC_ERR;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.SYNC_ERR;
    endfunction
    
    task run_tests();
        super.run_tests();
        // finally clear all queues
        `spi_frame_begin
        `spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #100us;
    endtask
    
    task apply_interrupt_condition();
        `spi_frame_begin
        `spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
        `spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'd1000;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #100us;
        `spi_frame_begin
        `spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'(1 << channel);)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #100us;
    endtask
endclass