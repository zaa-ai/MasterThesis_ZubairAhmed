/**
 * Class: tdma_scheme_pdcm_factory
 * 
 * Factory for different (random and concrete) PDCM TDMA schemes.
 */
class tdma_scheme_pdcm_factory extends uvm_object;
	
	`uvm_object_utils(tdma_scheme_pdcm_factory)

	function new(string name="tdma_scheme_pdcm_factory");
		super.new(name);
	endfunction

	static function tdma_scheme_pdcm single_packet(int symbol_count = $urandom_range(64,4), int chiptime = 3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		tdma_scheme_pdcm scheme = new("single_packet_PDCM_scheme");
		int earliest_start = random_earliest_start(bit_time);
		int latest_start = random_latest_start(earliest_start);
		
		scheme.chiptime = chiptime;
		scheme.bit_time =  bit_time;
		scheme.add_packet(tdma_scheme_packet_pdcm::new_packet(earliest_start, latest_start, symbol_count, dsi3_pkg::SID_0Bit));
		
		return scheme;
	endfunction
		
	static function tdma_scheme_pdcm single_packet_with_words(logic[15:0] words[$], int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		logic[3:0] data[$];
		if (convert_queue#(16, 4)::convert(words, data)) `uvm_error("tdma_scheme_pdcm", $sformatf("queue of words could not be properly converted"))
		return single_packet_with_data(data, chiptime, bit_time);
	endfunction	
	
	static function tdma_scheme_pdcm single_packet_with_data(logic[3:0] data[$], int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		int earliest_start = random_earliest_start(bit_time);
		int latest_start = random_latest_start(earliest_start);
		tdma_scheme_pdcm scheme = new("single_packet_PDCM_scheme");
		tdma_scheme_packet tdma_packet;
		scheme.chiptime = chiptime;
		scheme.bit_time =  bit_time;
		
		tdma_packet = tdma_scheme_packet_pdcm::new_packet(earliest_start, latest_start, data.size(), dsi3_pkg::SID_0Bit);
		tdma_packet.packet.data = data;
		scheme.add_packet(tdma_packet);

		return scheme;
	endfunction	
		
	static function tdma_scheme_pdcm single_pdcm_packet(dsi3_pdcm_packet packet, int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		tdma_scheme_pdcm scheme = single_packet_with_data({}, chiptime, bit_time);
		scheme.packets[0].packet = packet;
		scheme.packets[0].symbol_count = packet.data.size();
		return scheme;
	endfunction
	
	static function tdma_scheme_pdcm no_answer();
		tdma_scheme_pdcm scheme = single_packet_with_data({});
		scheme.packets[0].enable = 1'b0;
		return scheme;
	endfunction
	
	static function tdma_scheme_pdcm multiple_pdcm_packets(dsi3_pdcm_packet packets[$], int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		int earliest_start = random_earliest_start(bit_time);
		int latest_start = random_latest_start(earliest_start);
		tdma_scheme_pdcm scheme = new("multiple_packets_PDCM_scheme");
		scheme.chiptime = chiptime;
		scheme.bit_time =  bit_time;
		
		foreach(packets[i]) begin
			tdma_scheme_packet tdma_packet;
			tdma_packet = tdma_scheme_packet_pdcm::new_packet(0, 0, packets[i].data.size(), dsi3_pkg::SID_0Bit);
			tdma_packet.packet.data = packets[i].data;
			scheme.add_packet(tdma_packet);
		end
		scheme.calculate_start_times(earliest_start, latest_start);
		
		return scheme;
	endfunction
    
    static function tdma_scheme_pdcm multiple_packets_with_words(logic[15:0] first_pkg[$], logic[15:0] second_pkg[$], int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
        int earliest_start = random_earliest_start(bit_time);
        int latest_start = random_latest_start(earliest_start);
        logic[3:0] data[$];
        
        tdma_scheme_pdcm scheme = new("multiple_packets_PDCM_scheme");
        tdma_scheme_packet tdma_packet;
        scheme.chiptime = chiptime;
        scheme.bit_time = bit_time;
        
        // first data packet in scheme
        if (convert_queue#(16, 4)::convert(first_pkg, data)) `uvm_error("tdma_scheme_pdcm", $sformatf("queue of words could not be properly converted"))
        tdma_packet = tdma_scheme_packet_pdcm::new_packet(earliest_start, latest_start, data.size(), dsi3_pkg::SID_0Bit);
        tdma_packet.packet.data = data;
        scheme.add_packet(tdma_packet);

        // second data packet in scheme
        if (convert_queue#(16, 4)::convert(second_pkg, data)) `uvm_error("tdma_scheme_pdcm", $sformatf("queue of words could not be properly converted"))
        // calculate the start time of second data packet: duration of the first packet plus some tolerance
        earliest_start += first_pkg.size()*4*chiptime*3 + 100;
        latest_start   += first_pkg.size()*4*chiptime*3 + 100;
        tdma_packet = tdma_scheme_packet_pdcm::new_packet(earliest_start, latest_start, data.size(), dsi3_pkg::SID_0Bit);
        tdma_packet.packet.data = data;
        scheme.add_packet(tdma_packet);

        return scheme;
    endfunction
    
    // t__PDCM,START__ = 2 t__DSI,BIT__ + 5us
    static function int random_earliest_start(dsi3_pkg::dsi3_bit_time_e bit_time);
    	int min_start =  2 * dsi3_pkg::get_bit_time(bit_time) + 5;
    	int max_start = min_start + 50;
    	int earliest_start = $urandom_range(max_start, min_start);
    	return earliest_start;
    endfunction
    
    static function int random_latest_start(int earliest_start);
    	int latest_start = earliest_start + $urandom_range(50,10);
    	return latest_start;
    endfunction
	
endclass