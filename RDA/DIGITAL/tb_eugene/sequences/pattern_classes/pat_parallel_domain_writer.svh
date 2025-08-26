class pat_parallel_domain_writer extends pat_domain_writer;
	
	function new(int file_id);
		super.new(file_id);
	endfunction
	
	virtual function void write(pattern _pattern);
		pattern_domain	domain;
		write_signal_names(domain);
		write_domain_header(_pattern);
		write_domain_data(domain);
		write_domain_footer();
	endfunction
	
	protected virtual function void write_domain_header(pattern _pattern);
		string header = "  Domain ";
		for (int domain_index = 0; domain_index < _pattern.domains.size(); domain_index++) begin
			if (domain_index > 0)
				header = {header, ","};
			header = {header, _pattern.get_domain(domain_index).get_domain_name()};
		end
		header = {header, "\n"};
		$fwrite(file_id, header);
	endfunction
	
	protected virtual function void write_domain_data(pattern_domain domain);
		string pin_group_name = domain.get_pin_group_name();
		$fwrite(file_id, "not supported for now");
	endfunction
	
	protected virtual function void write_domain_footer();
		$fwrite(file_id, "    }\n");
	endfunction
	
endclass