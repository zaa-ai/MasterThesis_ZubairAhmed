custom_uvm_report_server my_report_server;

function void start_of_simulation_phase(uvm_phase phase);
	uvm_top.set_report_severity_id_action(UVM_WARNING, "RegModel", UVM_NO_ACTION); 
	// report configuration example:
	/*
	set_report_severity_action_hier(UVM_FATAL | UVM_LOG, UVM_DISPLAY);
	
	set_report_id_action_hier("elip_bus_monitor", UVM_NO_ACTION);
	set_report_id_action_hier("common_checker", UVM_NO_ACTION);
	set_report_id_action_hier("digital_signal_driver", UVM_NO_ACTION);
	set_report_id_action_hier("digital_signal_monitor", UVM_NO_ACTION);
	set_report_id_action_hier("osc_driver", UVM_NO_ACTION);
	set_report_id_action_hier("osc_monitor", UVM_NO_ACTION);
	set_report_id_action_hier("m_driver", UVM_NO_ACTION);
	set_report_id_action_hier("EAS_SCOREBOARD", UVM_NO_ACTION);
	set_report_id_action_hier("RegModel", UVM_NO_ACTION);
	*/
endfunction: start_of_simulation_phase