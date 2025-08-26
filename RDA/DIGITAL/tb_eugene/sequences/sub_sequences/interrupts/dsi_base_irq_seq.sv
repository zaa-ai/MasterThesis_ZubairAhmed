/*------------------------------------------------------------------------------
 * File          : dsi_base_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class dsi_base_irq_seq extends hierachical_irq_check_seq;
    
    `uvm_object_utils(dsi_base_irq_seq) 
    
    constraint co_channel { channel_based == 1'b1;};
    
    function new(string name = "DSI_base_irq_seq");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_irq_stat_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.DSI;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.DSI;
    endfunction
    
    virtual function uvm_reg_data_t channeled_sub_value(bit value);
        uvm_reg_data_t ch_value = 64'(value);
        return ch_value;
    endfunction
    
    virtual function uvm_reg_data_t channeled_value(bit value);
        uvm_reg_data_t ch_value = 64'(value << channel);
        return ch_value;
    endfunction
    
    // IRQ_MASK.DSI[3:0] 
    virtual task set_interrupt_mask(bit value);
        uvm_reg_field irq_mask_field = get_irq_mask_field();
        irq_mask_field.write(status, 64'(value << channel));
    endtask
    
    virtual task set_sub_interrupt_mask(bit value);
        uvm_reg_data_t field_value = 64'(value);
        uvm_reg_field sub_irq_mask_field = get_sub_irq_mask_field();
        sub_irq_mask_field.write(status, field_value);
    endtask
endclass