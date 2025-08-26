/**
 * Class: tdma_scheme
 * 
 * Base class for TDMA informations
 */
class tdma_scheme extends uvm_object;
	
	rand int					 	chiptime;
	rand dsi3_pkg::dsi3_bit_time_e 	bit_time;
	
	rand int symbol_count_min;
	rand int symbol_count_max;
	
	rand tdma_scheme_packet	packets[$];
	
	`uvm_object_utils_begin (tdma_scheme)
		`uvm_field_int (chiptime, UVM_DEFAULT)
		`uvm_field_enum(dsi3_pkg::dsi3_bit_time_e, bit_time, UVM_DEFAULT)
		`uvm_field_queue_object (packets, UVM_DEFAULT)
	`uvm_object_utils_end
	
	constraint co_chip_time {chiptime inside {[2:5]};}
	constraint co_chip_time_dist {chiptime dist {2:=5, 3:=10, 4:=5, 5:=5};}
	constraint co_paket_count {soft packets.size() <= 15;}
	constraint co_symbol_counts {symbol_count_min <= symbol_count_max;}
	constraint co_symbol_min {soft symbol_count_min > 4; soft symbol_count_min < 32;}
	constraint co_symbol_max {soft symbol_count_max > 4; soft symbol_count_max < 64;}
	
	function void post_randomize();
		for (int i = 0; i < packets.size(); i++) begin
			tdma_scheme_packet next_packet = create_packet();
			int earliest_start;

			if(i == 0) begin
				// t__PDCM,start__ 
				earliest_start = 2*dsi3_pkg::get_bit_time(bit_time)+5;
			end
			else begin
				earliest_start = packets[i-1].calculate_endtime_of_packet(chiptime) + 6*chiptime;
			end
			
			next_packet.set_tolerance_limits(0.95, 1.05);
			next_packet.crc_error_injection = RANDOM_ERROR;
			next_packet.chip_length_error_injection = NEVER_ERROR;
			next_packet.symbol_coding_error_injection = NEVER_ERROR;
			
			if(!next_packet.randomize() with {
					enable == 1'b1; 
					symbol_count inside {[symbol_count_min:symbol_count_max]}; 
					earliest_start_time inside {[earliest_start : earliest_start+50]}; 
					latest_start_time inside {[earliest_start_time+10 : earliest_start_time+50]};
					}) begin
				`uvm_error(get_type_name(), "failed to randomize TDMA scheme packet")
			end
			packets[i] = next_packet;		
		end
	endfunction
	
	virtual function tdma_scheme_packet create_packet();
		`uvm_error(get_type_name(), "create packet function has to be overridden by subclass")
		return null;
	endfunction
	
	// constraint c0 {tolerance_int inside {[900:1100]};}
	
	function new(string name = "tdma_scheme");
		super.new(name);
		chiptime = 3;
		bit_time = dsi3_pkg::BITTIME_8US;
		packets = {};
	endfunction
	
	virtual function void add_packet(tdma_scheme_packet packet);
		packets.push_back(packet);
	endfunction
	
	/**
	 * Gets number of enabled TDMA scheme packets.
	 */
	virtual function int get_packet_count();
		int count;
		count = 0;
		foreach(packets[i]) begin
			if(packets[i].enable) count++;
		end
		return count;
	endfunction
	
	virtual function void do_record(uvm_recorder recorder);
		`uvm_record_field("chiptime", $sformatf("%1dus",chiptime))
		`uvm_record_field("packet_count", packets.size())
		foreach (packets[i]) begin
			`uvm_record_field($sformatf("packet[%2d]", i), packets[i].convert2string())
		end
	endfunction
endclass


