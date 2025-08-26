class ldo_uv_debounce_measure_seq extends debounce_measure_seq;
	
	`uvm_object_utils(ldo_uv_debounce_measure_seq)

	function new(string name = "ldo_uv_debounce_measure");
		super.new(name);
		parameter_name = "t__CLDO,UV__";
		debounce_min = 5us;
		debounce_max = 15us;
	endfunction
	
	virtual task prepare_condition();
		clear_all_irqs();
		regmodel.Supply.supply_registers.SUP_IRQ_MASK.write(status, 16'd0);
		regmodel.Supply.supply_registers.SUP_IRQ_MASK.LDOUV.write(status, 16'd1);
	endtask
	
	virtual task apply_condition();
		set_cldo_uv(1'b1);
	endtask
	
	virtual task release_condition();
		set_cldo_uv(1'b0);
	endtask

	virtual task wait_for_condition();
		if(get_intb() == 1'b1) @(negedge intb.D);
	endtask
endclass