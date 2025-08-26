interface class pattern_domain_writer;
	pure virtual function void write(pattern _pattern);
	pure virtual function void set_use_pattern_repeats(bit enable);
endclass