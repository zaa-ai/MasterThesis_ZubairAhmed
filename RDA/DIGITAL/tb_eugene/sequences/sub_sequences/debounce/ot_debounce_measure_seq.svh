class ot_debounce_measure_seq extends debounce_measure_seq;
	
	`uvm_object_utils(ot_debounce_measure_seq)

	function new(string name = "ot_debounce_measure");
		super.new(name);
		parameter_name = "t__OT,deb__";
		debounce_min = 5us;
		debounce_max = 15us;
	endfunction
	
	virtual task prepare_condition();
		clear_all_irqs();
		regmodel.Supply.supply_registers.SUP_IRQ_MASK.write(status, 16'd0);
		regmodel.Supply.supply_registers.SUP_IRQ_MASK.OTE.write(status, 16'd1);
	endtask
	
	virtual task apply_condition();
		set_temp(175, 1ns);
	endtask
	
	virtual task release_condition();
		set_temp(25, 1ns);
	endtask

	virtual task wait_for_condition();
		if(get_intb() == 1'b1) @(negedge intb.D);
	endtask
	
	virtual task finalize();
		regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
endclass