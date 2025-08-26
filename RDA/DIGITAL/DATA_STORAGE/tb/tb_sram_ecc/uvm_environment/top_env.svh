/**
 * Class: top_env
 * 
 * TODO: Add class documentation
 */
class top_env extends uvm_env;

	`uvm_component_utils(top_env)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	elip_bus_agent			_elip_ram_agent;
	elip_bus_agent			_elip_jtag_agent;
	
	top_config				_top_config;
	
	function void build_phase(uvm_phase phase);
		if (!uvm_config_db #(top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end
		
		/*###   ELIP   ######################################################*/
		_top_config._elip_ram_agent = elip_bus_agent::type_id::create("_elip_ram_agent", this);
		agent_factory #(elip_bus_config)::register_config("_elip_ram_agent", _top_config._elip_ram_config, this);
		
		_top_config._elip_jtag_agent = elip_bus_agent::type_id::create("_elip_jtag_agent", this);
		agent_factory #(elip_bus_config)::register_config("_elip_jtag_agent", _top_config._elip_jtag_config, this);
		
		/*###   checking   ######################################################*/
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
	endfunction
	
	task run_phase(uvm_phase phase); //FIXME: check if needed
		phase.raise_objection(this);
		@_top_config.stop_uvm;
		`uvm_info(this.get_type_name, "Simulation end triggered", UVM_INFO)
		#10us;
		phase.drop_objection(this);
	endtask : run_phase
	
endclass
