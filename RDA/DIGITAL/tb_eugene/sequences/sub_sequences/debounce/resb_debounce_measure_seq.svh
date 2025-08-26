class resb_debounce_measure_seq extends debounce_measure_seq;
	
	`uvm_object_utils(resb_debounce_measure_seq)

	function new(string name = "resb_debounce_measure");
		super.new(name);
		parameter_name = "t__RESB,deb__";
		debounce_min = 700ns;
		debounce_max = 1600ns;
	endfunction
	
	virtual task run_tests();
		set_clock_ref(.enable(1'b0));
		super.run_tests();
		set_clock_ref(.enable(1'b1));
		#500us;
	endtask

	virtual task apply_condition();
		set_resb(0);
	endtask
	
	virtual task release_condition();
		set_resb(1);
	endtask
	
	virtual task wait_for_condition();
		if(get_rfc() == 1'b1) @(negedge rfc.D);
	endtask
endclass