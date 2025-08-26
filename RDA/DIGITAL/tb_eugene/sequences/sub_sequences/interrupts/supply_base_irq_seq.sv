/*------------------------------------------------------------------------------
 * File          : supply_base_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class supply_base_irq_seq extends hierachical_irq_check_seq;
    
    `uvm_object_utils(supply_base_irq_seq)
    
    constraint co_channel { channel == 0;};
    
    function new(string name = "SUPPLY_base_irq_seq");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_irq_stat_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.SUPPLY;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.SUPPLY;
    endfunction
endclass