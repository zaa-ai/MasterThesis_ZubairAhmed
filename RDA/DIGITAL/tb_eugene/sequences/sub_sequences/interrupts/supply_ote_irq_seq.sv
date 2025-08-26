/*------------------------------------------------------------------------------
 * File          : supply_ote_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class supply_ote_irq_seq extends supply_base_irq_seq;
    
    `uvm_object_utils(supply_ote_irq_seq) 
    
    function new(string name = "SUPPLY.OTE");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTE;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.Supply.supply_registers.SUP_IRQ_MASK.OTE;   
    endfunction
    
    task apply_interrupt_condition();
        // Disable LDOUV and OTW during this test, OTE trigger these two interrupts too
        regmodel.Supply.supply_registers.SUP_IRQ_MASK.LDOUV.write(status,1'b0);
        regmodel.Supply.supply_registers.SUP_IRQ_MASK.OTW.write(status,1'b0);
        set_temp(175, 10us);
        #100us;
    endtask
    
    task release_interrupt_condition();
        set_temp(25, 10us);
        #100us;
        // enable transceiver again and clear LDOUV and OTW
        regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status,4'hF);
        #300us;
        regmodel.Supply.supply_registers.SUP_IRQ_STAT.LDOUV.write(status,1'b1);
        regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTW.write(status,1'b1);
    endtask
endclass