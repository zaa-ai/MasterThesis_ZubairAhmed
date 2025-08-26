class base_irq_check_seq extends base_dsi_master_seq;
    
    `uvm_object_utils(base_irq_check_seq) 
    
    function new(string name = "base_irq_check_seq");
        super.new(name);
    endfunction
    
    virtual task run_tests();
        log_sim_description($sformatf("interrupt and mask test for %s", get_name()), LOG_LEVEL_SEQUENCE);
        
        clear_all_irqs();
        check_intb(1'b1);
        set_interrupt_mask(1'b1);
        
        log_sim_description($sformatf("check %s interrupt", get_name()), LOG_LEVEL_OTHERS);
        
        apply_interrupt_condition();
        check_intb(1'b0);
        
        release_interrupt_condition();
        
        log_sim_description($sformatf("check %s interrupt mask", get_name()), LOG_LEVEL_OTHERS);
        set_interrupt_mask(1'b0);
        #10us;
        check_intb(1'b1);
        
        set_interrupt_mask(1'b1);
        #10us;
        check_intb(1'b0);
        
        check_and_clear_irq_stat_register();
        check_all_irqs(64'd0);
        check_intb(1'b1);
    endtask
    
    virtual function uvm_reg_field get_irq_stat_field();
        `uvm_error(this.get_type_name(), "function 'get_irq_stat_field' has to be overridden by sub classes");
        return null;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        `uvm_error(this.get_type_name(), "function 'get_irq_mask_field' has to be overridden by sub classes");
        return null;
    endfunction
    
    virtual task set_interrupt_mask(bit value);
        uvm_reg_field irq_mask_field = get_irq_mask_field();
        registers.write_and_check_field(irq_mask_field, uvm_reg_data_t'(value));
    endtask
    
    virtual task apply_interrupt_condition();
    endtask
    
    virtual task release_interrupt_condition();
    endtask
    
    virtual task check_and_clear_irq_stat_register();
        uvm_reg_field irq_stat_field = get_irq_stat_field();
        registers.check_flag(irq_stat_field, 1'b1);
		
		// IRQ flag must not be cleared by writing a zero
		irq_stat_field.write(status, 1'b0);
		registers.check_flag(irq_stat_field, 1'b1);
		
        // clear the interrupt flag
        irq_stat_field.write(status, 1'b1);
		registers.check_flag(irq_stat_field, 1'b0);
    endtask
    
    virtual task check_all_irqs(uvm_reg_data_t expected_value);
        registers.check_register(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT, expected_value);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, expected_value);
        registers.check_register(regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT, expected_value);
        registers.check_register(regmodel.Supply.supply_registers.SUP_IRQ_STAT, expected_value);
        registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT, expected_value);
        registers.check_register(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT, expected_value);
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT, expected_value);
        end
    endtask
endclass
