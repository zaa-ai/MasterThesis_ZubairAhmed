/*------------------------------------------------------------------------------
 * File          : dsi_iq_err_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class dsi_iq_err_irq_seq extends dsi_base_irq_seq;
    
    `uvm_object_utils(dsi_iq_err_irq_seq) 
    
    function new(string name = "DSI.IQ_ERR");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.IQ_ERR;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.IQ_ERR;
    endfunction
    
    task apply_interrupt_condition();
        set_iload(5000.0/1000.0, channel);
        
        #100us;
        
        `spi_frame_begin
            `spi_frame_create(spi_measure_quiescent_current_seq, channel_bits == (2'b01 << channel);)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end

        #100us;
        
    endtask
    
    task release_interrupt_condition();
        set_iload(0.0/1000.0, channel);
    endtask
endclass