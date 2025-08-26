/**
 * A container class for flags/bits. This class can be typed by an enumeration that contains all the flags.
 * Can be used as a base class for objects that contain a set of status flags. 
 */
class flags_container #(type T) extends uvm_object;

	bit flags[T];
	`uvm_object_param_utils_begin(flags_container#(T))
		`uvm_field_aa_int_enumkey(T, flags, UVM_DEFAULT)
	`uvm_object_utils_end
	
	function new(string name = "flags_container");
		super.new(name);
		initialize();
	endfunction
	
	virtual function bit get_value(T index);
		return flags[index];
	endfunction
	
	virtual function int get_values();
		int value=0;
		T iterator = iterator.first();
		do begin
			value[iterator] = flags[iterator];
			iterator = iterator.next();
		end while (iterator != iterator.first());
		return value;
	endfunction
	
	virtual function void set_values(int value);
		T iterator = iterator.first();
		do begin
			flags[iterator] = value[iterator];
			iterator = iterator.next();
		end while (iterator != iterator.first());
	endfunction
	
	virtual function void set_value(T index, bit value);
		flags[index] = value;
	endfunction
	
	virtual function void set_flags(T flags_to_set[$]);
		while (flags_to_set.size() > 0) begin
			flags[flags_to_set[0]] = 1'b1;
			flags_to_set.pop_front();
		end
	endfunction
	
	/**
	 * Checks a given value against a given expectation.
	 * returns 1 if there is any error
	 */
	virtual function bit check_value(T index, bit expected_value, string message_context = "");
		if (index.name() == "SCI")
		begin
			expected_value = 1'b0;
		end
		if (flags[index] != expected_value) begin
			`uvm_error(this.get_type_name(), $sformatf("%s Flag %s was not set correctly! Exp. %1b but got %1b", message_context, index.name(), expected_value, flags[index]))
			return 1'b1;
		end
		return 1'b0;
	endfunction
	
	virtual function void check_values(int expected_value);
		T iterator = iterator.first();
		do begin
			check_value(iterator, expected_value[iterator]);
			iterator = iterator.next();
		end while (iterator != iterator.first());
	endfunction
	
	/**
	 * Checks a given value against a given expectation.
	 * returns 1 if there is any error
	 */
	virtual function bit check_flags_are_equal(flags_container#(T) _flag_container, string message_context = "", T ignore_flags[$] = {});
		bit error = 1'b0;
		foreach (flags[index]) begin
			bit ignore = 1'b0;
			foreach(ignore_flags[i]) begin
				if(index == ignore_flags[i]) begin
					ignore = 1'b1;
				end
			end
			if (ignore == 1'b0 && _flag_container.flags.exists(index)) begin
				if(check_value(index, _flag_container.flags[index], message_context) == 1'b1) begin
					error = 1'b1;
				end
			end
		end
		return error;
	endfunction
	
	protected virtual function void initialize();
		T iterator = iterator.first();
		do begin
			flags[iterator] = 1'b0;
			iterator = iterator.next();
		end while (iterator != iterator.first());
	endfunction
	
endclass
