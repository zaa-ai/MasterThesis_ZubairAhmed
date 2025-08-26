/*------------------------------------------------------------------------------
 * File          : dsi_dsiov_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class dsi_dsiov_irq_seq extends dsi_base_irq_seq;
    
    `uvm_object_utils(dsi_dsiov_irq_seq) 
    
    function new(string name = "DSI.DSIOV");
        super.new(name);        
    endfunction : new       
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_sub_irq_stat_field();        
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DSIOV;     
    endfunction     
    
    virtual function uvm_reg_field get_sub_irq_mask_field();        
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.DSIOV;     
    endfunction     
    
    task apply_interrupt_condition();       
        set_dsi_ov_for_channel(channel, 1'b1);      
        #5500us;        
    endtask     
    
    task release_interrupt_condition();     
        set_dsi_ov_for_channel(channel, 1'b0);      
        #5500us;        
        regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 64'hF);        
    endtask             
endclass