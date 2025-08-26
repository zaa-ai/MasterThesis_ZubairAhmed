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
	
	top_config				_top_config;
	
	elip_bus_agent			_elip_agent;
	
	check_elip				_check_elip;
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end
		
		/*###   ELIP   ######################################################*/
		_elip_agent = elip_bus_agent::type_id::create("elip_agent", this);
		agent_factory #(elip_bus_config)::register_config("elip_agent", _top_config._elip_config, this);
		
		_top_config._elip_register_agent = elip_bus_agent::type_id::create("elip_register_agent", this);
		agent_factory #(elip_bus_config)::register_config("elip_register_agent", _top_config._elip_register_config, this);
		
		/*###   checking   ######################################################*/
		_check_elip = check_elip::type_id::create("_check_elip", this);
		_top_config._check_elip = _check_elip;
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		/*###   ELIP checking   ######################################################*/
		_elip_agent.analysis_port.connect(_check_elip.elip_export);
		_top_config._elip_register_agent.analysis_port.connect(_check_elip.elip_register_export);
		_top_config._check_elip = _check_elip;
	endfunction
	
	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		@_top_config.stop_uvm;
		`uvm_info(this.get_type_name, "Simulation end triggered", UVM_INFO)
		#10us;
		phase.drop_objection(this);
	endtask : run_phase
	
endclass
