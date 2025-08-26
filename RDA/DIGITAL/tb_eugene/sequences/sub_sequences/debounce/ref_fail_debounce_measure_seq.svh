class ref_fail_debounce_measure_seq extends debounce_measure_seq;
	
	`uvm_object_utils(ref_fail_debounce_measure_seq)

	function new(string name = "ref_fail_debounce_measure");
		super.new(name);
		parameter_name = "t__VBGerr,deb__";
		debounce_min = 70us;
		debounce_max = 80us;
	endfunction
	
	virtual task prepare_condition();
		clear_all_irqs();
		regmodel.Supply.supply_registers.SUP_IRQ_MASK.write(status, 16'd0);
		regmodel.Supply.supply_registers.SUP_IRQ_MASK.REF_FAIL.write(status, 16'd1);
	endtask
	
	virtual task apply_condition();
		set_ref_fail(1'b1);
	endtask
	
	virtual task release_condition();
		set_ref_fail(1'b0);
	endtask

	virtual task wait_for_condition();
		if(get_intb() == 1'b1) @(negedge intb.D);
	endtask
endclass