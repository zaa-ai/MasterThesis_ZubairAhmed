/**
 * Class: agent_factory
 * 
 * TODO: Add class documentation
 */
class agent_factory #(type T) extends uvm_component;

	function new(string name="agent_factory", uvm_component parent=null);
		super.new(name, parent);
	endfunction
	
//	static function T create_agent(string name, uvm_component parent);
//		T _agent = T::type_id::create("name", this);
//		return _agent;
//	endfunction
	
	static function void register_config(string agent_name, T config_object, uvm_component parent);
		uvm_config_db #(T)::set(parent, agent_name, "config", config_object);
		if (config_object.is_active == UVM_ACTIVE )
			uvm_config_db #(T)::set(parent, {agent_name,".m_sequencer"}, "m_config", config_object);
	endfunction

endclass


