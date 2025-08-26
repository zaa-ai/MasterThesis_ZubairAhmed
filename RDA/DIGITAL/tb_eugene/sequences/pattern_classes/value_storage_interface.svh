interface class value_storage_interface;
	pure virtual function logic[31:0]	get_value();
	pure virtual function int	get_size();
	pure virtual function string_stream get_signal_name();
	pure virtual function void	sample();
	pure virtual function int	is_output();
	pure virtual function void	set_direction(int is_output);
	pure virtual function int	get_direction();
endclass
