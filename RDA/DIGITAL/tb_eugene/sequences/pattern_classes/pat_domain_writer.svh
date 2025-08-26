virtual class pat_domain_writer implements pattern_domain_writer;
	
	protected bit use_pattern_repeats;
	protected int file_id;
	
	protected int pattern_repeats;
	protected string last_vector;
	protected pat_signal_writer writer;
	protected string timeplate_name;
	
	function new (int file_id);
		this.file_id = file_id;
		writer = new();
	endfunction
	
	protected virtual function void write_signal_names(pattern_domain domain);
		string_stream	names;
		string empty_space = "";
		bit reverted=1'b0;
		repeat (domain.get_pin_group_name().len())
			empty_space = {empty_space, " "};
		names = domain.get_vector_description(writer);
		for (int line = 0; line < names.size(); line++)
			names[line] = {"  #                 ",empty_space, names[line]};
		if (reverted)
			for (int line = names.size()-1; line >= 0; line--)
				$fwrite(file_id, {names[line],"\n"});
		else
			for (int line = 0; line < names.size() ; line++)
				$fwrite(file_id, {names[line],"\n"});
	endfunction
	
	pure virtual function void write(pattern _pattern);
	
	protected virtual function void write_vectors(pattern_domain domain);
		pattern_repeats = 0;
		for (int index = 0; index < domain.get_pattern_count(); index++) begin
			write_vector_line(domain, index, get_comment(domain, index));
		end
	endfunction
	
	protected virtual function void write_vector_line(pattern_domain domain, int index, string comment);
		string new_vector;
		bit is_last = (domain.get_pattern_count()-1 == index) ? 1'b1 : 1'b0;
		bit is_first = (index == 0) ? 1'b1 : 1'b0;
		string	vector = "";
		if ((index%5000)==0)
			$display("wrote line %6d of %6d", index, domain.get_pattern_count());
		new_vector = get_vector_line_end(domain, domain.get_vector_line(writer), is_first, comment);
		if (use_pattern_repeats) begin
			if (is_first) begin
				last_vector = new_vector;
				pattern_repeats = 1;
			end
			else begin
				if (new_vector == last_vector) begin
					pattern_repeats++;
					if (is_last)
						write_previous_vector(domain, last_vector, pattern_repeats, is_last);
				end
				else begin
					write_previous_vector(domain, last_vector, pattern_repeats, is_last);
					last_vector = new_vector;
					pattern_repeats = 1;
				end
			end
		end
		else
			write_previous_vector(domain, new_vector, pattern_repeats, is_last);
	endfunction
	
	protected virtual function void write_previous_vector(pattern_domain domain,string last_vector_end, int repeats, bit is_last);
		string operator;
		if (is_last) begin
			if (repeats > 1)
				write_previous_vector(domain, last_vector_end, repeats-1, 1'b0);
			operator = "EXIT      ";
			repeats = 1;
		end
		else begin
			if (repeats > 2)	operator = $sformatf("IDXI %5d", repeats-1);
			else				operator = $sformatf("NOP       ");
		end
		if (repeats == 2)
			write_vector(domain, operator, last_vector_end);
		write_vector(domain, operator, last_vector_end);
	endfunction
	
	protected virtual function void write_vector(pattern_domain domain, string operator, string vector_end);
		string vector_line;
		vector_line = $sformatf("    %s {V{%s= %s", operator, domain.get_pin_group_name() , vector_end);
		$fwrite(file_id, vector_line);
	endfunction
	
	protected virtual function string get_vector_line_end(pattern_domain domain, string vector, bit is_first, string comment);
		string vector_line;
		vector_line = $sformatf("%s;}", vector);
		if (is_first)	vector_line = $sformatf("%s  W{%s= %s;}", vector_line, domain.get_pin_group_name(), timeplate_name);
		vector_line = {vector_line, "}", comment};
		return vector_line;
	endfunction
	
	
	protected virtual function string get_comment(pattern_domain domain, int index);
		string current_comment = domain.get_comment(index);
		if (current_comment != "")	current_comment = $sformatf("#  %s\n",current_comment);
		else						current_comment = $sformatf("\n");
		return current_comment;
	endfunction
	
	virtual function void set_use_pattern_repeats(bit enable);
		use_pattern_repeats = enable;
	endfunction
	
	virtual function void set_timeplate(string timeplate);
		this.timeplate_name = timeplate;
	endfunction
	
endclass