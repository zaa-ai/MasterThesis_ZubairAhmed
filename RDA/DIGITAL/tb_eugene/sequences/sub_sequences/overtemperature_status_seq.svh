class overtemperature_status_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(overtemperature_status_seq)

	function new(string name = "");
		super.new("overtemperature_status");
	endfunction
	
	task run_tests();
		
		log_sim_description("check over temperature status registers", LOG_LEVEL_SEQUENCE);
		
		set_temp(25, 10us);
		#500us;
		regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
		#100us;
	    check_temperature_status_registers(1'b0, 1'b0);
	    set_temp(130, 10us);
	    #100us;
	    check_temperature_status_registers(1'b1, 1'b0);
	    set_temp(175, 10us);
		check_temperature_status_registers(1'b1, 1'b1);
		
		set_temp(25, 10us);
		#100us;
		check_temperature_status_registers(1'b0, 1'b0);
	endtask
	
	task check_temperature_status_registers(bit ot_warning, bit ot_error);
		uvm_reg_data_t value;
		// clear IRQs
		regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTW.write(status, 1);
		regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTE.write(status, 1);
		// check warning
		regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTW.read(status, value);
		if(1'(value) != ot_warning) `uvm_error(this.get_name(), $sformatf("Unexpected OTW flag in register SUP_IRQ_STAT, expected %1b, got %1b", ot_warning, value))
		regmodel.Supply.supply_registers.SUP_STAT.OTW.read(status, value);
		if(1'(value) != ot_warning) `uvm_error(this.get_name(), $sformatf("Unexpected OTW flag in register SUP_STAT, expected %1b, got %1b", ot_warning, value))
		// check error
		regmodel.Supply.supply_registers.SUP_IRQ_STAT.OTE.read(status, value);
		if(1'(value) != ot_error) `uvm_error(this.get_name(), $sformatf("Unexpected OTE flag in register SUP_IRQ_STAT, expected %1b, got %1b", ot_error, value))
		regmodel.Supply.supply_registers.SUP_STAT.OTE.read(status, value);
		if(1'(value) != ot_error) `uvm_error(this.get_name(), $sformatf("Unexpected OTE flag in register SUP_STAT, expected %1b, got %1b", ot_error, value))
	endtask
endclass
