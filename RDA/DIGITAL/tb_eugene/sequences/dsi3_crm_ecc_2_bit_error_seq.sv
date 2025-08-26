class dsi3_crm_ecc_2_bit_error_seq extends dsi3_crm_ecc_1_bit_error_seq;

	`uvm_object_utils(dsi3_crm_ecc_2_bit_error_seq)

	function new(string name = "");
		super.new("dsi3_crm_ecc_2_bit_error");
        set_name("dsi3_crm_ecc_2_bit_error");
		bit_error = TWO_BIT_ERR;
	endfunction
	virtual task run_tests();
		log_sim_description("Testcase for double bit ECC failures", LOG_LEVEL_TOP);
		// disable automatic check for HE flag
		get_checker_config().enable_hardware_error_check = 1'b0;
		super.run_tests();
	endtask
endclass
