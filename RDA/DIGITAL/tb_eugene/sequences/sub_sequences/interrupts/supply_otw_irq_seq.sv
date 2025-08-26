/*------------------------------------------------------------------------------
 * File          : supply_otw_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class supply_otw_irq_seq extends supply_base_irq_seq;
    
    `uvm_object_utils(supply_otw_irq_seq) 
    
    function new(string name = "SUPPLY.OTW");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTW;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.Supply.supply_registers.SUP_IRQ_MASK.OTW;   
    endfunction
    
    task apply_interrupt_condition();
        set_temp(130, 10us);
        #100us;
    endtask
    
    task release_interrupt_condition();
        set_temp(25, 10us);
        #100us;
    endtask
endclass
