virtual class value_storage#(type T) implements value_storage_interface;
	T vif;
	protected logic[31:0]	value[$];
	protected time	period;
	protected int	size;
	protected string name[$];
	protected int	_is_output;
	
	protected bit	enable_sampling;
	
	protected logic[31:0] previous_value;
	protected bit	powered_up;
	protected int	powerup_counter;
	protected int	edge_counter;
	protected bit	edge_detected;
	
	protected time x_before_edge;
	protected time x_after_edge;
	
	protected time x_powerup;
	
	function new(time period, T _vif, string name[$], int size=1);
		this.period = period;
		value.delete();
		edge_counter = 0;
		previous_value = '0;
		this.vif = _vif;
		this.name = name;
		this.size = size;
		this.x_before_edge = 0;
		this.x_after_edge = 0;
		this.x_powerup = 0;
		this.enable_sampling = 1'b1;
	endfunction
	
	virtual function void set_sampling(bit on);
		enable_sampling = on;
	endfunction
	
	virtual function logic[31:0] get_value();
		check_for_edge();
		
		if ((powered_up == 0)) begin
			powerup_counter++;
			if (powerup_counter*period > x_powerup)
				powered_up = 1;
			previous_value = value.pop_front();
			return 'x;
		end
		
		if ((has_edge(x_before_edge))) begin
			previous_value = value.pop_front();
			return 'x;
		end
		
		if (edge_detected) begin
			if (edge_counter*period < x_after_edge) begin
				previous_value = value.pop_front();
				edge_counter++;
				return 'x;
			end
			else begin
				edge_detected = 0;
				edge_counter = 0;
				previous_value = value.pop_front();
				return previous_value;
			end
		end
		
		previous_value = value.pop_front();
		return previous_value;
	endfunction
	
	protected virtual function void check_for_edge();
		if (previous_value != value[0]) begin
			edge_detected = 1;
			edge_counter = 0;
		end
	endfunction
	
	protected virtual function int get_number_of_samples(time sample_time);
		return sample_time/period;
	endfunction
	
	protected virtual function bit has_edge(time time_to_edge);
		logic[31:0] initial_value = value[0];
		bit edge_detected = 1'b0;
		int samples = get_number_of_samples(time_to_edge);
		for (int index = 0; index < samples; index++) begin
			if (value[index] != initial_value) begin
				edge_detected = 1'b1;
				break;
			end
		end
		return edge_detected;
	endfunction
	
	pure virtual function void sample();
	
	virtual function int get_size();
		return size;
	endfunction

	virtual function string_stream get_signal_name();
		return name;
	endfunction
	
	virtual function int is_output();
		return _is_output;
	endfunction
	
	virtual function void set_direction(int is_output);
		this._is_output = is_output;
	endfunction
	
	virtual function int get_direction();
		return this._is_output;
	endfunction
endclass
