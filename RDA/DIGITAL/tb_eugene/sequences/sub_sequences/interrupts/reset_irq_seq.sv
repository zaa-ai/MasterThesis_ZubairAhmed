/*------------------------------------------------------------------------------
 * File          : reset_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class reset_irq_seq extends base_irq_check_seq;
    
    `uvm_object_utils(reset_irq_seq) 
    
    function new(string name = "IRQ_STAT.RESET");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_irq_stat_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.RESET;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.RESET;
    endfunction
    
    task apply_interrupt_condition();
        set_resb(0);
        #100us;
        set_resb(1);
        @(posedge rfc.D);
        #500us;
        regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.CLKREF.write(status, 64'b1); // clear CLKREF IRQ
        #100us;
    endtask
endclass