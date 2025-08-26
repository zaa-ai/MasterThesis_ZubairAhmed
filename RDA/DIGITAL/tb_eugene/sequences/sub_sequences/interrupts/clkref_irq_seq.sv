/*------------------------------------------------------------------------------
 * File          : clkref_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class clkref_irq_seq extends base_irq_check_seq;
    
    osc_tr osc;
    
    `uvm_object_utils(clkref_irq_seq) 
    
    function new(string name = "IRQ_STAT.CLKREF");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_irq_stat_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.CLKREF;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.CLKREF;
    endfunction
    
    task apply_interrupt_condition();
        `uvm_do_on_with (osc, m_osc_agent.m_sequencer, {enabled == 0; freq==400000;})
        #200us;
    endtask
    
    task release_interrupt_condition();
        `uvm_do_on_with (osc, m_osc_agent.m_sequencer, {enabled == 1; freq==500000;})
        #500us;
    endtask
endclass