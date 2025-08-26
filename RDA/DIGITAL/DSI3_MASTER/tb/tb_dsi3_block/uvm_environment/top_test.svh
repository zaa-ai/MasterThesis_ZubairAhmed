/**
 * Class: top_test
 * 
 * Top UVM test class for DSI3 block unit tests
 */
class top_test extends uvm_test;

	`uvm_component_utils(top_test)

	top_env m_env;

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		m_env = top_env::type_id::create("m_env", this);
	endfunction
	
endclass
