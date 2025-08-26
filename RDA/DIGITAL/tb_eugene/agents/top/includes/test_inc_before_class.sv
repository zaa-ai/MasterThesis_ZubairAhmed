/**
 * Class: custom_uvm_report_server
 * 
 * Customized report server
 */
class custom_uvm_report_server extends uvm_default_report_server;
	
	function string get_type_name();
		return "custom_uvm_report_server";
	endfunction
	
	function string getfilename(string path);
		int find = 0;
		int len = path.len();
		for (int i = 0; i < len; i=i+1) begin
			if (path.getc(i) == "/" ) begin
				find = i;
			end
		end
		return path.substr(find, path.len()-1);
	endfunction : getfilename
	
	function string fill_with_spaces(string str, int length);
		string tempstr=str;
		for (int i=str.len(); i<length; i++)
			tempstr = {tempstr," "};
		return tempstr;
	endfunction : fill_with_spaces
	
	virtual function string compose_report_message(uvm_report_message report_message, string report_object_name = "");

		string sev_string;
		uvm_severity l_severity;
		uvm_verbosity l_verbosity;
		string filename_line_string;
		string time_str;
		string line_str;
		string context_str;
		string verbosity_str;
		string terminator_str;
		string msg_body_str;
		string id_str;
		uvm_report_message_element_container el_container;
		string prefix;
		uvm_report_handler l_report_handler;

		l_severity = report_message.get_severity();
		sev_string = fill_with_spaces(l_severity.name(), 11);

		if (report_message.get_filename() != "") begin
			line_str.itoa(report_message.get_line());
//			filename_line_string = {" \t", getfilename(report_message.get_filename()), "(", line_str, ") "};
			filename_line_string = {" \t", report_message.get_filename(), "(", line_str, ") "};
		end

		// Make definable in terms of units.
		$swrite(time_str, "%15.7fus", $realtime/1.0us);
 
		if (report_message.get_context() != "")
			context_str = {"@@", report_message.get_context()};

		if (show_verbosity) begin
			if ($cast(l_verbosity, report_message.get_verbosity()))
				verbosity_str = l_verbosity.name();
			else
				verbosity_str.itoa(report_message.get_verbosity());
			verbosity_str = {"(", verbosity_str, ")"};
		end

		if (show_terminator)
			terminator_str = {" -",sev_string};

		el_container = report_message.get_element_container();
		if (el_container.size() == 0)
			msg_body_str = report_message.get_message();
		else begin
			prefix = uvm_default_printer.knobs.prefix;
			uvm_default_printer.knobs.prefix = " +";
			msg_body_str = {report_message.get_message(), "\n", el_container.sprint()};
			uvm_default_printer.knobs.prefix = prefix;
		end

		if (report_object_name == "") begin
			l_report_handler = report_message.get_report_handler();
			report_object_name = l_report_handler.get_full_name();
		end
		
		id_str = report_message.get_id();
		id_str = {" [", id_str, "] "};
		id_str = fill_with_spaces(id_str, 25);
		
		compose_report_message = {sev_string, verbosity_str, "@ ", time_str, ": ", /*report_object_name, context_str,*/ id_str, msg_body_str, " ", filename_line_string, terminator_str};

	endfunction 


endclass


