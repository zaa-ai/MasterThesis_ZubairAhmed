`ifndef TDMA_CONFIG_SV
`define TDMA_CONFIG_SV

class tdma_config extends uvm_object;

	// Do not register config class with the factory
	
	virtual	tdma_interface vif;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	bit	coverage_enable;       
	bit	checks_enable;
	
	function new(string name = "");
		super.new("tdma_config");
	endfunction
	

endclass 

`endif
