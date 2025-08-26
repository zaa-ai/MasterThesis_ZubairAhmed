virtual class pattern_writer;
	protected int file_id;
	protected string timeplate_name;
	
	virtual function void write_pattern(string file_name, pattern _pattern);
		file_id = $fopen(file_name, "w");
		do_write_pattern(_pattern);
		$fclose(file_id);
	endfunction
	
	protected pure virtual function void do_write_pattern(pattern _pattern);
	
	virtual function void set_timeplate(string timeplate_name);
		this.timeplate_name = timeplate_name;
	endfunction
	
endclass