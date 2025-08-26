class pat_pattern_writer#(
	string TIMING			= "all_pat_Timing.tim",
	string PIN_DESCRIPTION	= "PinDesc.pin",
	string PXR				= "rec_pat.pxr"
) extends pattern_writer;
	protected bit use_repeats;
	protected bit serial_domains;
	
	function new(bit use_repeats, bit serial_domains);
		super.new();
		this.use_repeats = use_repeats;
		this.serial_domains = serial_domains;
	endfunction
	
	protected virtual function void do_write_pattern(pattern _pattern);
		write_header();
		write_domains(_pattern);
		write_footer();
	endfunction
	
	virtual function void write_pattern(string file_name, pattern _pattern);
		super.write_pattern({file_name,".pat"}, _pattern);
	endfunction
	
	protected virtual function void write_header();
		$fwrite(file_id, "# PAT writer\n\n");
		$fwrite(file_id, "Version 1.0;\n");
		$fwrite(file_id, "MainPattern {\n");
		$fwrite(file_id, " CommonSection {\n");
		$fwrite(file_id, {"  Timing           \"",TIMING,":rec_pat_Timing\";\n"});
		$fwrite(file_id, {"  PinDescription   \"",PIN_DESCRIPTION, "\";\n"});
		$fwrite(file_id, {"  Pxr              \"", PXR, "\";\n"});
		
	endfunction
	
	protected virtual function void write_domains(pattern _pattern);
		pat_domain_writer	domain_writer;
		if (serial_domains) begin
			domain_writer = pat_serial_domain_writer::new(file_id);
		end
		else begin
			domain_writer = pat_parallel_domain_writer::new(file_id);
		end
		domain_writer.set_timeplate(timeplate_name);
		domain_writer.set_use_pattern_repeats(use_repeats);
		domain_writer.write(_pattern);
	endfunction
	
	protected virtual function void write_footer();
		$fwrite(file_id, "  }\n");
		$fwrite(file_id, "}\n");
	endfunction
	
endclass