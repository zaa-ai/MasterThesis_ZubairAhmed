class register_dsi_irq_en_frontdoor_access_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_dsi_irq_en_frontdoor_access_seq)
	
	function new(string name = "");
		super.new("register_dsi_irq_en_frontdoor_access");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("check frontdoor access (read/write) to DSI_IRQ_MASK register of each channel", LOG_LEVEL_SEQUENCE);
		
		repeat(10) begin
			foreach(regmodel.DSI[channel]) begin
				uvm_reg_data_t value;
				logic[15:0] irq_value ={10'd0, 6'($urandom())};
				
				regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.write(status, irq_value);
				if(status != UVM_IS_OK) `uvm_error(this.get_name(), $sformatf("Failed to write DSI_IRQ_MASK register to value %0h, UVM status is not OK.", irq_value))
				
				regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.read(status, value);
				if(status != UVM_IS_OK) `uvm_error(this.get_name(), $sformatf("Failed to read value from DSI_IRQ_MASK register, UVM status is not OK."))
				if(value != 64'(irq_value)) `uvm_error(this.get_name(), $sformatf("Read unexpected value from DSI_IRQ_MASK register, expected %0h, got %0h.", irq_value, value))
			end
		end
		#10us;
	endtask
endclass