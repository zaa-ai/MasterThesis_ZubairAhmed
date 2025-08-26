
class sram_bist_seq extends base_dsi_master_seq;

	protected int rows[4] = {21, 100, 0, 191};
	protected int cols[4] = { 5, 100, 0, 367};
	
	parameter string path_to_RAM = "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_data_storage.i_ram_wrapper_ecc_with_bist.utils_sram_with_bist_inst.utils_sram_scan_shell_inst.sync_sram_inst.sram_inst.mem";

	`uvm_object_utils(sram_bist_seq)

	function new(string name = "");
		super.new("sram_bist");
	endfunction

	virtual task run_tests();
		log_sim_description("Testcase for SRAM BIST", LOG_LEVEL_TOP);
		initialize();
		check_reset_value_of_status();
		start_sram_bist_with_pattern();
		
		for (int bitwise = 0; bitwise < 2; bitwise++) begin
			for (int four_6n = 0; four_6n < 2; four_6n++) begin
				start_sram_bist_and_check_pass(.f6n(four_6n), .bitwise(bitwise));
				check_sram_bist_fail(.f6n(four_6n), .bitwise(bitwise));
			end
		end
		start_sram_bist_and_check_pass(.f6n(0), .bitwise(0));
	endtask

	virtual task initialize();
		log_sim_description("Initialize JTAG", LOG_LEVEL_OTHERS);
		jtag_enable_with_tdo(1'b1);
		#10us;
	endtask
	
	virtual task start_sram_bist_with_pattern();
		time start_time;
		log_sim_description($sformatf("check SRAM BIST with ECPS pattern pass"), LOG_LEVEL_SEQUENCE);
		begin
			M52144A_pattern_wrapper	wrapper;
			wrapper = get_pattern_wrapper();
			pattern_enable();
			wrapper.run_test_top_TM_RAM_BIST_start();
			pattern_disable();
		end
		start_time = $time();
		while (start_time+4ms > $time()) begin
			begin
				M52144A_pattern_wrapper	wrapper;
				wrapper = get_pattern_wrapper();
				pattern_enable();
				wrapper.run_test_top_TM_RAM_BIST_result();
				pattern_disable();
			end
		end
		
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.EN.write(status, 1'b0);
		check_reset_value_of_status();
	endtask

	virtual task start_sram_bist_and_check_pass(int f6n, int bitwise);
		time	run_time;
		log_sim_description($sformatf("check SRAM BIST with FOUR_6N = %1d BITWISE = %1d pass", f6n, bitwise), LOG_LEVEL_SEQUENCE);
		
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.EN.set(1'b1);
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.FOUR_6N.set(f6n[0]);
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.BITWISE.set(bitwise[0]);
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.update(status);
		
		wait_for_BIST_finished(run_time);
        if ((f6n == 0) && (bitwise == 0))
		    log_sim_measure("t__SRAM_BIST__", $sformatf("%7.2f",(run_time)/1.0ms), $sformatf("Config: FOUR_6N = %1d, BITWISE = %1d", f6n, bitwise));
        else
            `uvm_info(this.get_type_name(), $sformatf("'t__SRAM_BIST__' = '%7.2fus' condition = 'Config: FOUR_6N = %1d, BITWISE = %1d'",(run_time)/1.0ms, f6n, bitwise), UVM_INFO)
		check_status(bist_pkg::BIST_PASS);
		
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.EN.write(status, 1'b0);
		#1us;
		check_reset_value_of_status();
		#1us;
	endtask
	
	virtual task check_sram_bist_fail(int f6n, int bitwise);
		log_sim_description($sformatf("check SRAM BIST with FOUR_6N = %1d BITWISE = %1d fail", f6n, bitwise ), LOG_LEVEL_SEQUENCE);
		for (int fval = 0; fval < 2; fval++) begin
			for (int row = 0; row < 4; row++) begin
				for (int col = 0; col < 4; col++) begin
					start_sram_bist_and_check_fail(f6n, bitwise,  rows[row], cols[col], fval);
				end
			end
		end
	endtask

	virtual task start_sram_bist_and_check_fail(int f6n, int bitwise, int row, int col, int force_val);
		time	run_time;
		string path_to_RAMcell = $sformatf("%s[%1d][%1d]", path_to_RAM, row, col);
		string force_val_str = $sformatf("%1d", force_val[0]);
		log_sim_description($sformatf("check SRAM BIST with FOUR_6N = %1d BITWISE = %1d fail (row=%3d, column=%3d, force value=%8h", f6n, bitwise, row, col, force_val), LOG_LEVEL_OTHERS);

		$hdl_xmr_force(path_to_RAMcell, force_val_str, , , ,0);
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.EN.set(1'b1);
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.FOUR_6N.set(f6n[0]);
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.BITWISE.set(bitwise[0]);
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.update(status);
		
		wait_for_BIST_finished(run_time);
		if(!run_time > 0) `uvm_error(this.get_name(), "unexpected BIST execution time")
		check_status(bist_pkg::BIST_FAIL);
		
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_CTRL.EN.write(status, 1'b0);
		$hdl_xmr_release(path_to_RAMcell, 0);
		#1us;
		check_reset_value_of_status();
		#1us;
	endtask

	virtual task check_reset_value_of_status();
		check_status(bist_pkg::BIST_INIT);
	endtask
	
	virtual task check_status(bist_pkg::bist_status_t expected);
		uvm_reg_data_t value;
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_STAT.STATUS.read(status, value);
		if(bist_pkg::bist_status_t'(value) != expected) begin
			`uvm_error(this.get_type_name(), $sformatf("unexpected value for SRAM BIST status, expected %04h, got %04h", expected, value))
		end
	endtask
	
	virtual task wait_for_BIST_finished(output time run_time);
		uvm_reg_data_t value;
		time start_time, end_time;
		start_time = $time();
		do begin
			#10us;
			test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_BIST_STAT.STATUS.read(status, value);
		end while (bist_pkg::bist_status_t'(value) == bist_pkg::BIST_BUSY);
		end_time = $time();
		run_time = end_time-start_time;
	endtask
endclass
