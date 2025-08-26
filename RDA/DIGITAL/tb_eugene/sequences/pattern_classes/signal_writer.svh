interface class signal_writer;
	pure virtual function string append_signal_value(string line, logic value, bit is_output);
	pure virtual function string_stream append_signal_name(string_stream line, string signal);
endclass