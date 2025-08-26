class pat_serial_domain_writer extends pat_domain_writer;
	
	function new(int file_id);
		super.new(file_id);
	endfunction
	
	virtual function void write(pattern _pattern);
		pattern_domain	domain;
		for (int domain_index = 0; domain_index < _pattern.domains.size(); domain_index++) begin
			domain = _pattern.domains[domain_index];
			write_signal_names(domain);
			write_domain_header(domain);
			write_domain_data(domain);
			write_domain_footer();
		end
	endfunction
	
	protected virtual function void write_domain_header(pattern_domain domain);
		string header = $sformatf("  Domain %s  {\n",domain.get_domain_name());
		$fwrite(file_id, header);
	endfunction
	
	protected virtual function void write_domain_data(pattern_domain domain);
		string pin_group_name = domain.get_pin_group_name();
		write_vectors(domain);
	endfunction
	
	protected virtual function void write_domain_footer();
		$fwrite(file_id, "    }\n");
	endfunction
	
endclass