class pattern_domain_iterator extends pattern_domain;
	protected pattern_domain signals;
	protected int value_index; // index of value in signal
	protected int signal_index; // index of signals
	protected logic[31:0] previous_value;
	
	function new(pattern_domain signals);
		super.new(signals.period, "", "");
		this.signals = signals;
		value_index = 0;
		signal_index = 0;
	endfunction
	
	function bit has_next();
		if (signal_index < signals.signals.size())
			return 1'b1;
	endfunction
	
	function void next();
		if (value_index >= signals.signals[signal_index].get_size()-1) begin
			signal_index++;
			value_index=0;
		end
		else begin
			value_index++;
		end
	endfunction
	
	function logic get_value();
		if (value_index == 0)
			previous_value = signals.signals[signal_index].get_value();
		return previous_value[value_index];
	endfunction
	
	function string get_name();
		string_stream name;
		name = signals.signals[signal_index].get_signal_name();
		return name[value_index];
	endfunction
	
	function void reset();
		signal_index=0;
		value_index = 0;
	endfunction
	
	function bit is_output();
		int _is_output;
		_is_output = signals.signals[signal_index].is_output();
		return _is_output[value_index];
	endfunction
	
endclass