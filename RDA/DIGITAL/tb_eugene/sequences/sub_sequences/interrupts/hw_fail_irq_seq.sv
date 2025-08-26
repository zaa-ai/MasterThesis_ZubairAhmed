/*------------------------------------------------------------------------------
 * File          : hw_fail_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class hw_fail_irq_seq extends base_irq_check_seq;
    
    `uvm_object_utils(hw_fail_irq_seq) 
    
    function new(string name = "IRQ_STAT.HW_FAIL");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_irq_stat_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.HW_FAIL;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.HW_FAIL;
    endfunction
    
    task apply_interrupt_condition();
        hdl_force(`STRING_OF(`MAIN_STATE_PATH), 'hF);
        #20us;
        hdl_release(`STRING_OF(`MAIN_STATE_PATH));
        #500us;
        regmodel.Supply.supply_registers.SUP_IRQ_STAT.REF_FAIL.write(status, 64'b1);
    endtask
endclass