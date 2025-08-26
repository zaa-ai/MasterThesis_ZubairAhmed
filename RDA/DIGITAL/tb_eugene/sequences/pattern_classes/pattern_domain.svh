typedef pattern_domain_iterator;
class pattern_domain;
	protected value_storage_interface signals[$];
	protected time	period;
	event			stop_sampling_event;
	protected int	count;
	protected string comment;
	protected string comments[$];
	protected string pin_group_name;
	protected string domain_name;
	
	function new(time period, string pin_group_name, string domain_name);
		this.period = period;
		count = 0;
		this.pin_group_name = pin_group_name;
		this.domain_name = domain_name;
	endfunction
	
	virtual function void add_signal(value_storage_interface signal);
		signals.push_back(signal);
	endfunction
	
	virtual function void start_sampling();
		fork
			do_sampling();
		join_none
	endfunction
	
	protected virtual task do_sampling();
		fork
			forever begin
				sample_comment();
				foreach(signals[signal]) begin
					signals[signal].sample();
				end
				count++;
				#period;
			end
			begin
				@stop_sampling_event;
			end
		join_any
		disable fork;
	endtask
	
	virtual function void stop_sampling();
		-> stop_sampling_event;
	endfunction
	
	virtual function int get_pattern_count();
		return count;
	endfunction
	
	virtual function void set_comment(string comment);
		this.comment = comment;
	endfunction
	
	virtual function string get_pin_group_name();
		return pin_group_name;
	endfunction
	
	virtual function string get_comment(int index);
		return comments[index];
	endfunction
	
	virtual function string get_domain_name();
		return domain_name;
	endfunction
	
	protected virtual function void sample_comment();
		comments.push_back(comment);
		if (comment != "") begin
			comment = "";
		end
	endfunction
	
	protected virtual function logic_bitstream_t get_values(value_storage_interface signal);
		logic_bitstream_t values;
		logic[31:0] signal_value = signal.get_value();
		for (int signal_value_index = 0; signal_value_index < signal.get_size(); signal_value_index++) begin
			values.push_back(signal_value[signal_value_index]);
		end
		return values;
	endfunction
	
	virtual function string get_vector_line(signal_writer writer);
		pattern_domain_iterator iterator;
		string line = "";
		iterator = new(this);
		while (iterator.has_next()) begin
			line = writer.append_signal_value(line, iterator.get_value(), iterator.is_output());
			iterator.next();
		end
		return line;
	endfunction
	
	virtual function string_stream get_vector_description(signal_writer writer);
		pattern_domain_iterator iterator;
		string line[$];
		iterator = new(this);
		while (iterator.has_next()) begin
			line = writer.append_signal_name(line, iterator.get_name());
			iterator.next();
		end
		return line;
	endfunction
	
endclass