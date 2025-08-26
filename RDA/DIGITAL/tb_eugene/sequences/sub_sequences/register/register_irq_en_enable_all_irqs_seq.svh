class register_irq_en_enable_all_irqs_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_irq_en_enable_all_irqs_seq)
	
	function new(string name = "");
		super.new("register_irq_en_enable_all_irqs");
	endfunction : new
	
	virtual task run_tests();
		uvm_reg_data_t value;
		logic[15:0] expected = 16'h1E7F;
		log_sim_description("enable all IRQs in IRQ_MASK register", LOG_LEVEL_SEQUENCE);
				
		regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.write(status, 16'h0000);
		regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.write(status, expected);
		regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.read(status, value);
		if(value != 64'(expected)) `uvm_error(this.get_name(), $sformatf("Read unexpected value from IRQ_MASK register, expected %0h, got %0h.", expected, value))
		#10us;
	endtask
endclass