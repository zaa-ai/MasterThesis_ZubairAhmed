/**
 * Class: register_util
 *
 * Different register related helper tasks and functions.
 */
class register_util extends uvm_report_object;

	uvm_status_e status;
	simulation_logger logger;
	
	function new(string name, simulation_logger sim_logger);
		super.new(name);
		logger = sim_logger;
	endfunction

	task check_flag(uvm_reg_field field, uvm_reg_data_t expected_value, bit measure_register = 1'b0);
		uvm_reg_data_t    read_value;
		field.read(status, read_value);
		check_register_field(field, expected_value, measure_register);
	endtask
	
	task write_and_check_field(uvm_reg_field field, uvm_reg_data_t expected_value);
		field.write(status, expected_value);
		check_flag(field, expected_value);
	endtask
	
	function void check_register_field(uvm_reg_field field, uvm_reg_data_t expected_value, bit measure_register = 1'b0);
		//✅ Injected mistake: force incorrect expected value for COM_ERR
     	if (field.get_name() == "COM_ERR") begin
         	expected_value = 1'b0; // Engineer assumes it should not be set
     	end
		if (expected_value != field.get()) begin
			if(field.get_n_bits() > 1) begin
				`uvm_error(this.get_name(), $sformatf("%s is not set correctly. Got 0x%0h but expected 0x%0h (%s)", field.get_name() , field.get(), expected_value, field.get_full_name()))
			end 
			else begin
				`uvm_error(this.get_name(), $sformatf("%s is not set correctly. Got %1b but expected %1b (%s)", field.get_name() , field.get(), expected_value, field.get_full_name()))
			end
			if(measure_register == 1'b1) begin
				logger.log_sim_check(field.get_register().get_name(), .status("FAIL"));
			end
		end
		else begin
			logger.log_sim_check(field.get_register().get_name(), .status("PASS"));
		end
	endfunction
	
	task write_and_check_register(uvm_reg register, uvm_reg_data_t expected_value);
		register.write(status, expected_value);
		check_register(register, expected_value);
	endtask
	
	task check_register(uvm_reg register, uvm_reg_data_t expected_value);
		uvm_reg_data_t value;
		register.read(status, value);
		if (expected_value != value) begin
			`uvm_error(this.get_name(), $sformatf("%s is not set correctly. Got %4h but expected %4h (%s)", register.get_name() , value, expected_value, register.get_full_name()))
			logger.log_sim_check(register.get_name(), .status("FAIL"));
		end
		else begin
			logger.log_sim_check(register.get_name(), .status("PASS"));
		end
	endtask

	task reset_field(uvm_reg_field field);
		uvm_reg_data_t reset_value;
		reset_value = field.get_reset();
		field.write(status, reset_value);
		if(status != UVM_IS_OK) `uvm_error(this.get_name(), $sformatf("Failed to reset field %s, UVM status is not OK.", field.get_name()))
	endtask
	
	task reset_register(uvm_reg register);
		uvm_reg_data_t reset_value;
		reset_value = register.get_reset();
		register.write(status, reset_value);
		if(status != UVM_IS_OK) `uvm_error(this.get_name(), $sformatf("Failed to reset %s register, UVM status is not OK.", register.get_name()))
	endtask

endclass

