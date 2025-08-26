/*------------------------------------------------------------------------------
 * File          : buf_dsi_crm_data_fe_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class buf_dsi_crm_data_fe_irq_seq extends buf_base_irq_seq;
    
    `uvm_object_utils(buf_dsi_crm_data_fe_irq_seq) 
    
    function new(string name = "BUF.BUF_DSI_CRM_DATA_FE");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.DSI_CRM_FE;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_MASK.DSI_CRM_FE;
    endfunction
    
    task apply_interrupt_condition();
        dsi3_crm_packet packets[$];
        create_valid_CRM_packets_with_data(packets);
        
        `spi_frame_begin
        repeat(128 / 3 + 1) begin
            `spi_frame_create(spi_crm_seq, channel_bits == 2'(1 << channel); broad_cast == 1'b0;)
        end
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #(((128 / 3) + 1) * 500us);
    endtask
endclass