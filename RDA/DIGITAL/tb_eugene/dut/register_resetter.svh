/**
 * Class: register_resetter
 * 
 * class to reset register models or blocks
 */
class register_resetter extends uvm_subscriber #(digital_signal_tr);
	
	uvm_reg_block	reg_model;
	
	`uvm_component_utils(register_resetter)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	virtual function void write(digital_signal_tr t);
		if (t.value == 1'b0)
			reg_model.reset();
	endfunction

endclass
