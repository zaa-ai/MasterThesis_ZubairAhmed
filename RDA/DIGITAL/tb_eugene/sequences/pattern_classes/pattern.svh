class pattern;
	pattern_domain	domains[$];
	
	function new();
		// TODO: implement
	endfunction
	
	virtual function void add_domain(pattern_domain domain);
		domains.push_back(domain);
	endfunction
	
	virtual task start_sampling();
		foreach (domains[domain])
			domains[domain].start_sampling();
	endtask
	
	virtual function void stop_sampling();
		foreach (domains[domain])
			domains[domain].stop_sampling();
	endfunction
	
	virtual function void set_comment(string comment);
		foreach (domains[domain])
			domains[domain].set_comment(comment);
	endfunction
	
	virtual function pattern_domain get_domain(int index);
		if (index < domains.size())
			return domains[index];
		else begin
			$error("Domain with index %1d does not exist", index);
		end
		return null;
	endfunction
	
endclass