
interface class iterator_interface;
	
	pure virtual function bit has_next();
	
	pure virtual function int get_current();
	
	pure virtual task apply_next();
	
	pure virtual task apply_default();
	
	pure virtual function void restart();
	
endclass

class chip_times_iterator implements iterator_interface;
	localparam	shortint	max_chip_time = 5;
	localparam	shortint	initial_chip_time = 2;
	
	shortint chip_time;
	
	function new();
		restart();
	endfunction
	
	virtual function bit has_next();
		if(chip_time > max_chip_time) begin
			return 1'b0;
		end
		return 1'b1;
	endfunction
	
	virtual function int get_current();
		return chip_time;
	endfunction
	
	virtual task apply_current();
	endtask
	
	virtual task apply_next();
		chip_time++;
	endtask
	
	virtual task apply_default();
		chip_time = 3;
	endtask
		
	virtual function void restart();
		chip_time = initial_chip_time;
	endfunction
	
endclass

class chip_times_iterator_with_register_model extends chip_times_iterator;
	
	ral_sys_device_registers regmodel;

	function new(ral_sys_device_registers regmodel);
		super.new();
		this.regmodel = regmodel;
	endfunction
	
	virtual task apply_current();
		uvm_status_e status;
		uvm_reg_data_t value;
		if(chip_time <= max_chip_time) begin
			if(value != 0) `uvm_error("chip_time_iterator", $sformatf("Failed to write register field FAST_DSI3 to value 0"))
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CHIPTIME.write(status, chip_time - 2);
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CHIPTIME.read(status, value);
			if(value != uvm_reg_data_t'(chip_time - 2)) `uvm_error("chip_time_iterator", $sformatf("Failed to write register field CHIPTIME to value %0d", chip_time - 2))
		end
	endtask;
	
	virtual task apply_next();
		apply_current();
		chip_time++;
	endtask;
		
	virtual task apply_default();
		uvm_status_e status;	
		uvm_reg_data_t chiptime_reset = regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CHIPTIME.get_reset();
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CHIPTIME.write(status, chiptime_reset);
	endtask
		
endclass 

class chipt_time_iterator_for_unit_tests extends chip_times_iterator;
	
	virtual dsi3_common_config_if common_config;
	
	function new(virtual dsi3_common_config_if common_config);
		super.new();
		this.common_config = common_config;
	endfunction
	
	virtual task apply_current();
		case (chip_time)
			2,3,4,5: begin
				common_config.chip_time = 2'(chip_time - 16'd2);
			end
		endcase
	endtask;
	
	virtual task apply_next();
		apply_current();
		chip_time++;
	endtask;
		
	virtual task apply_default();
		common_config.chip_time = '1;
	endtask
		
endclass
