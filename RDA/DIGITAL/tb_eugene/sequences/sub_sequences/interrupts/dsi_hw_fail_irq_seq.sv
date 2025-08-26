/*------------------------------------------------------------------------------
 * File          : dsi_hw_fail_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class dsi_hw_fail_irq_seq extends dsi_base_irq_seq;
    
    `uvm_object_utils(dsi_hw_fail_irq_seq) 
    
    function new(string name = "DSI.HW_FAIL");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.HW_FAIL;
    endfunction
    
    task apply_interrupt_condition();
        `uvm_info(this.get_type_name(), $sformatf("force"), UVM_INFO)
        hdl_force($sformatf(`STRING_OF(`DSI_STATE_PATH), channel), 'h1F);
        #20us;
    endtask
    
    task release_interrupt_condition();
        `uvm_info(this.get_type_name(), $sformatf("release"), UVM_INFO)
        hdl_release($sformatf(`STRING_OF(`DSI_STATE_PATH), channel));
        #20us;
    endtask
endclass