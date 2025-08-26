/*------------------------------------------------------------------------------
 * File          : buf_base_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class buf_base_irq_seq extends hierachical_irq_check_seq;
    
    `uvm_object_utils(buf_base_irq_seq) 
    
    function new(string name = "buf_base_irq_seq");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_irq_stat_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.BUF;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.BUF;
    endfunction
endclass