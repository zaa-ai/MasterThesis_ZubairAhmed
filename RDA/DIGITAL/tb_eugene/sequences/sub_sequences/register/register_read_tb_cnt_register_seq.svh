class register_read_tb_cnt_register_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_read_tb_cnt_register_seq)
	
	function new(string name = "");
		super.new("register_read_tb_cnt_register");
	endfunction : new
	
	virtual task run_tests();
		uvm_reg_data_t last_value;
		log_sim_description("Read TB_CNT register", LOG_LEVEL_SEQUENCE);
		
		regmodel.Timebase.time_base_registers.TB_CNT.read(status, last_value);
		repeat(10) begin
			uvm_reg_data_t value;
			regmodel.Timebase.time_base_registers.TB_CNT.read(status, value);
			if(value == last_value) `uvm_error(this.get_type_name(), $sformatf("expected different value for subsequent TB_CNT register reads, got two times: 0x%0h", value));
			last_value = value;
		end
	endtask
endclass