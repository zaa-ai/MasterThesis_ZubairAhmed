/*------------------------------------------------------------------------------
 * File          : hierachical_irq_check_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class hierachical_irq_check_seq extends base_irq_check_seq;
    
    rand int channel;
    rand bit channel_based;
    string channel_info;
    
    `uvm_object_utils(hierachical_irq_check_seq) 
    
    function new(string name = "hierachical_irq_check_seq");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        channel_info = (channel_based == 1'b1) ? $sformatf(" at channel %1d", channel) : "";
        log_sim_description($sformatf("interrupt and mask test for %s%s", get_name(), channel_info), LOG_LEVEL_SEQUENCE);
        
        clear_all_irqs();
        check_intb(1'b1);
        set_interrupt_mask(1'b1);
        set_sub_interrupt_mask(1'b1);
        
        log_sim_description($sformatf("check %s interrupt%s", get_name(), channel_info), LOG_LEVEL_OTHERS);
        
        apply_interrupt_condition();
        check_intb(1'b0);
        
        release_interrupt_condition();
        
        check_masking(1'b0, 1'b1);
        check_masking(1'b1, 1'b0);
        check_masking(1'b0, 1'b0);
        
        check_and_clear_irq_stat_register();
        check_all_irqs(64'd0);
    endtask
    
    virtual task check_masking(bit irq_mask, bit sub_irq_mask);
        log_sim_description($sformatf("check %s interrupt mask %s=%1b and %s=%1b%s", get_name(), get_irq_mask_field().get_name(), irq_mask, get_sub_irq_mask_field().get_name(), sub_irq_mask, channel_info), LOG_LEVEL_OTHERS);
        
        set_interrupt_mask(irq_mask);
        set_sub_interrupt_mask(sub_irq_mask);
        #10us;
        check_intb(1'b1);
        
        set_interrupt_mask(1'b1);
        set_sub_interrupt_mask(1'b1);
        check_intb(1'b0);
    endtask
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        `uvm_error(this.get_type_name(), "function 'get_sub_irq_stat_field' has to be overridden by sub classes");
        return null;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        `uvm_error(this.get_type_name(), "function 'get_sub_irq_mask_field' has to be overridden by sub classes");
        return null;
    endfunction
    
    virtual task set_sub_interrupt_mask(bit value);
        uvm_reg_data_t field_value = channeled_sub_value(value);
        uvm_reg_field sub_irq_mask_field = get_sub_irq_mask_field();
        registers.write_and_check_field(sub_irq_mask_field, field_value);
    endtask
    
    virtual task check_and_clear_irq_stat_register();
        uvm_reg_field irq_stat_field = get_irq_stat_field();
        uvm_reg_field sub_irq_stat_field = get_sub_irq_stat_field();
        
        uvm_reg_data_t value = channeled_value(1'b1);
        uvm_reg_data_t sub_value = channeled_sub_value(1'b1);
        
        registers.check_flag(irq_stat_field, value);
        registers.check_flag(sub_irq_stat_field, sub_value);
        sub_irq_stat_field.write(status, sub_value); // clear the interrupt flag
    endtask
    
    virtual function uvm_reg_data_t channeled_sub_value(bit value);
        uvm_reg_data_t ch_value = 64'(value << channel);
        return ch_value;
    endfunction
    
    virtual function uvm_reg_data_t channeled_value(bit value);
        uvm_reg_data_t ch_value = 64'(value);
        return ch_value;
    endfunction
    
endclass