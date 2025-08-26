/*------------------------------------------------------------------------------
 * File          : supply_vccuv_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class supply_vccuv_irq_seq extends supply_base_irq_seq;
    
    `uvm_object_utils(supply_vccuv_irq_seq) 
    
    function new(string name = "SUPPLY.VCCUV");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.Supply.supply_registers.SUP_IRQ_STAT.VCCUV;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.Supply.supply_registers.SUP_IRQ_MASK.VCCUV; 
    endfunction
    
    task apply_interrupt_condition();
        // disable REF_FAIL IRQ for this test
        regmodel.Supply.supply_registers.SUP_IRQ_MASK.REF_FAIL.write(status, 1'b0);
        set_vcc_uv(1'b1);
        #200us;
    endtask
    
    task release_interrupt_condition();
        set_vcc_uv(1'b0);
        #200us;
        // clear REF_FAIL IRQ for this test
        regmodel.Supply.supply_registers.SUP_IRQ_STAT.REF_FAIL.write(status, 1'b1);
    endtask
endclass