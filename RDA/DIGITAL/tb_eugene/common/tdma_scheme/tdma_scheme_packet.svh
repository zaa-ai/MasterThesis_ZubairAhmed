/**
 * Class: tdma_scheme_packet
 * 
 * TDMA scheme information for a packet send by a slave
 */
class tdma_scheme_packet extends uvm_object;
	/*###   scheme info   ######################################################*/
	rand shortint unsigned		earliest_start_time;
	rand shortint unsigned		latest_start_time;
	rand int unsigned			symbol_count;
	rand dsi3_pkg::sid_length_e	id_symbol_count;
	rand bit					enable;
	
	/*###   error_injection   ######################################################*/
	error_injection_e		crc_error_injection;
	error_injection_e		symbol_coding_error_injection;
	error_injection_e 		chip_length_error_injection;
	
	/*###   for test bench   ######################################################*/
	rand	time		start_time;
	real				tolerance;
	rand	int			tolerance_int;
	int					tolerance_int_min;
	int					tolerance_int_max;
	parameter	time time_unit	= 1us;
	time				fine_delay_time = 0ns;
	
	rand dsi3_packet packet;
	
	/*###   UVM automation   ######################################################*/
	`uvm_object_utils_begin (tdma_scheme_packet)
		`uvm_field_int  (earliest_start_time, UVM_DEFAULT)
		`uvm_field_int  (latest_start_time, UVM_DEFAULT)
		`uvm_field_int  (symbol_count, UVM_DEFAULT)
		`uvm_field_enum (dsi3_pkg::sid_length_e, id_symbol_count, UVM_DEFAULT)
		`uvm_field_int  (enable, UVM_DEFAULT)
		`uvm_field_int  (start_time, UVM_DEFAULT)
		`uvm_field_real (tolerance, UVM_DEFAULT)
		`uvm_field_int  (tolerance_int, UVM_DEFAULT)
		`uvm_field_int  (tolerance_int_min, UVM_DEFAULT)
		`uvm_field_int  (tolerance_int_max, UVM_DEFAULT)
		`uvm_field_int  (fine_delay_time, UVM_DEFAULT)
		`uvm_field_enum (error_injection_e, crc_error_injection, UVM_DEFAULT)
		`uvm_field_enum (error_injection_e, symbol_coding_error_injection, UVM_DEFAULT)
		`uvm_field_enum (error_injection_e, chip_length_error_injection, UVM_DEFAULT)
	`uvm_object_utils_end
	
	/************************ coverage ************************/
	covergroup cov_tdma_scheme_packet;
		option.per_instance = 0;
		cp_id_symbol_count : coverpoint id_symbol_count;
		cp_symbol_count : coverpoint symbol_count;
	endgroup
	
	/************************ constraints ************************/
	constraint co_time_valid   {earliest_start_time < latest_start_time -> start_time inside {[(time_unit * earliest_start_time):(time_unit * (latest_start_time))]};}
	
	// also accept invalid start times in order to test upload of invalid TDMA schemes
	constraint co_time_equal   {earliest_start_time == latest_start_time -> start_time  == (time_unit * latest_start_time);}
	constraint co_time_invalid {earliest_start_time > latest_start_time -> start_time inside {[(time_unit * latest_start_time):(time_unit * (earliest_start_time))]};}
	
	constraint co_time_order {solve earliest_start_time, latest_start_time before start_time;}
	constraint co_tol	{tolerance_int inside {[tolerance_int_min:tolerance_int_max]};}
	
	/************************ Methods declarations ************************/
	function void post_randomize();
		tolerance = get_tolerance_value(tolerance_int);
	endfunction

	function new(string name="tdma_scheme_packet");
		super.new(name);
		cov_tdma_scheme_packet = new();
	endfunction
	
	virtual function void set_packet_values(
			shortint unsigned earliest_start, 
			shortint unsigned latest_start,
			int unsigned symbols, 
			dsi3_pkg::sid_length_e id_symbols, 
			real tolerance_min=0.95, 
			real tolerance_max=1.05,
			error_injection_e crc_error_injection = RANDOM_ERROR, 
			error_injection_e symbol_coding_error_injection = NEVER_ERROR, 
			error_injection_e chip_length_error_injection = NEVER_ERROR);
		
		this.tolerance_int_min = get_tolerance_int_value(tolerance_min);
		this.tolerance_int_max = get_tolerance_int_value(tolerance_max);
		this.earliest_start_time = earliest_start;
		this.latest_start_time = latest_start;
		this.symbol_count = symbols;
		this.id_symbol_count = id_symbols;
		if(!this.randomize(start_time, tolerance_int)) `uvm_error(this.get_name(), "randomization error")
		this.enable = 1;
		this.crc_error_injection = crc_error_injection;
		this.symbol_coding_error_injection = symbol_coding_error_injection;
		this.chip_length_error_injection = chip_length_error_injection;
	endfunction
	
	static function tdma_scheme_packet get_from_queue(ref logic[15:0] queue[$]);
		tdma_scheme_packet packet = new();
		logic[15:0]	temp;
		packet.earliest_start_time = queue.pop_front();
		packet.latest_start_time = queue.pop_front();
		temp = queue.pop_front();
		packet.symbol_count = temp[7:0];
		packet.id_symbol_count = dsi3_pkg::sid_length_e'(temp[15:14]);
		packet.tolerance_int_min = get_tolerance_int_value(0.95);
		packet.tolerance_int_max = get_tolerance_int_value(1.05);
		packet.symbol_coding_error_injection = NOT_SET;
		packet.chip_length_error_injection = NOT_SET;
		packet.crc_error_injection = NOT_SET;
		return packet;
	endfunction
	
	virtual function time get_earliest_start_time();
		return (time_unit * earliest_start_time);
	endfunction

	virtual function time get_latest_start_time();
		return (time_unit * latest_start_time);
	endfunction
	
	virtual function void set_start_time_window(shortint unsigned earliest_start, shortint unsigned latest_start);
		this.earliest_start_time = earliest_start;
		this.latest_start_time = latest_start;
	endfunction
	
	virtual function time get_start_time();
		if(!this.randomize(start_time)) `uvm_error(this.get_name(), "randomization error")
		return start_time;
	endfunction
	
	virtual function real get_tolerance();
		if(!this.randomize(tolerance_int)) `uvm_error(this.get_name(), "randomization error")
		tolerance = get_tolerance_int_value(tolerance_int);
		return tolerance;
	endfunction
	
	virtual function void set_tolerance (real tolerance);
		this.tolerance = tolerance;
		this.tolerance_int = get_tolerance_int_value(tolerance);
	endfunction
	
	virtual function void set_tolerance_limits(real min, real max=min);
		this.tolerance_int_min = get_tolerance_int_value(min);
		this.tolerance_int_max = get_tolerance_int_value(max);
	endfunction
	
	static function real get_tolerance_value(int tol);
		return tol / 1000.0;
	endfunction
	
	static function int get_tolerance_int_value(real tol);
		return tol*1000;
	endfunction
	
	virtual function bit is_enabled();
		return enable;
	endfunction
	
	virtual function int get_word_count_of_data();
		int word_count = symbol_count / 4;
		if ((symbol_count % 4) > 0)
			word_count++;
		return word_count;
	endfunction
	
	virtual function void sample_cov();
		cov_tdma_scheme_packet.sample();
	endfunction
	
	/*###   transaction recording   ######################################################*/
	static function string get_table_header();
		return "symbols | id_symbol_count | earliest start | latest start";
	endfunction
	
	virtual function string convert2string();
		return $sformatf("%7d | %15d | %7d (%4h) | %5d (%4h)",
				symbol_count, id_symbol_count, earliest_start_time, earliest_start_time, latest_start_time, latest_start_time);
	endfunction
	
	virtual function void do_record(uvm_recorder recorder);
		`uvm_record_field("packet", convert2string())
	endfunction
	
	function int unsigned calculate_endtime_of_packet(int chiptime);
		int unsigned latest_packet_endtime = int'(latest_start_time + (((symbol_count * 3) * chiptime) * 1.05));
		return latest_packet_endtime;
	endfunction
endclass
