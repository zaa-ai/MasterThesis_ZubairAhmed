
typedef	enum int {
	// main (top level) logging 
	LOG_LEVEL_TOP = 0, 
	// sequence logging (e.g. description of a sequence or task)
	LOG_LEVEL_SEQUENCE = 1, 
	// less important information
	LOG_LEVEL_OTHERS = 2 
} simulation_log_level;

/**
 * Class: simulation_logger
 * 
 * Helper class for common logging of tests, sub tests and measurements. 
 * The resulting contents of simulation log can be parsed by other tools (e.g. stove or sim script).
 */
class simulation_logger extends uvm_report_object;
		
	localparam string ID_SIM_TASK  			= "sim:task";
	localparam string ID_SIM_DESCRIPTION  	= "sim:description";
	localparam string ID_SIM_STATUS  		= "sim:status";
	localparam string ID_SIM_MEASURE  		= "sim:measure";
	localparam string ID_SIM_END  			= "sim:end";
	
	function new(string name);
		super.new(name);
	endfunction
	
	/**
	 * Marks start of EDF simulation task.
	 * 
	 * <lineHeader> @ <time>: [sim:task] <simTaskName> : <description>
	 */
	function void log_sim_task(string task_name, string description = "");
		string text = $sformatf("%s", task_name);
		if(description != "") text = $sformatf("%s : %s", text, description);
		uvm_report_info (ID_SIM_TASK, text, UVM_NONE, , , "", 1);
	endfunction
	
	/**
	 * Adds a description to current task.
	 * 
	 * <lineHeader> @ <time>: [sim:description:<level>] <description>
	 */
	function void log_sim_description(string description, int level = 0);
		string message_id = ID_SIM_DESCRIPTION;
		string text = description;
		if(level == 0) begin
			text = $sformatf("'''%s'''", description); // EDF Wiki syntax for bold
		end
		if(level > 0) begin
			// append a '*' for each level (EDF Wiki syntax for lists)
			for (int i = 1; i <= level; i++) begin
				text = $sformatf("*%s", text);
			end
			message_id = $sformatf("%s:%0d", message_id, level);
		end
		uvm_report_info (message_id, text, UVM_NONE, , , "", 1);
	endfunction
	
	/**
	 * Adds a measurement (result) to a parameter that is contained in current task.
	 * 
	 * [<lineHeader>] @ <time>: [sim:measure] '<paramName>'='<value>' condition = '<conditionText>' status=[PASS|FAIL|OPEN]
	 */
	function void log_sim_measure (string parameter_name, string value, string condition = "", string status = "");
		string text = $sformatf("'%s' = '%s'", parameter_name, value);
		if(condition != "") text = $sformatf("%s condition = '%s'", text, condition);
		if(status != "") 	text = $sformatf("%s status = %s", text, status);
		uvm_report_info (ID_SIM_MEASURE, text, UVM_NONE, , , "", 1);
	endfunction
	
	/**
	 * Adds a none-parameter measurement that is contained in current task.
	 * 
	 * [<lineHeader>] @ <time>: [sim:measure] '<elementName>' condition = '<conditionText>' status=[PASS|FAIL|OPEN]
	 */
	function void log_sim_check (string element_name, string condition = "", string status = "");
		string text = $sformatf("'%s'", element_name);
		if(condition != "") text = $sformatf("%s condition = '%s'", text, condition);
		if(status != "") 	text = $sformatf("%s status = %s", text, status);
		uvm_report_info (ID_SIM_MEASURE, text, UVM_NONE, , , "", 1);
	endfunction
	
	/**
	 * Set status of current task.
	 * 
	 * [<lineHeader>] @ <time>: [sim:status] [PASS|FAIL|OPEN]
	 */
	function void log_sim_status (string status );
		uvm_report_info (ID_SIM_STATUS, status, UVM_NONE, , , "", 1);
	endfunction
	
	/**
	 * Finishes current task or marks successful end of simulation.
	 * 
	 * <lineHeader> [sim:end] <text>
	 */
	function void log_sim_end (string text = "");
		uvm_report_info (ID_SIM_END, text, UVM_NONE, , , "", 1);
	endfunction
			
endclass


