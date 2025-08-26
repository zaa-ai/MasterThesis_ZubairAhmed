/**
 * Class: tdma_scheme_dm
 * 
 * Valid TDMA scheme to be used for discovery mode.
 */
class tdma_scheme_dm extends tdma_scheme;

	function new(string name = "discovery_mode_TDMA_scheme", int number_of_slaves = 15);
		super.new(name);
		repeat(number_of_slaves) begin
			// initialize all DM packets with start times from t__Disc_dly,8__
			add_packet(tdma_scheme_packet_dm::new_packet(58,  70, 1));
		end
	endfunction
	
	virtual function tdma_scheme_packet create_packet();
		tdma_scheme_packet_dm packet = new();
		return packet;
	endfunction
	
	static function tdma_scheme valid(int number_of_slaves = 15);
		tdma_scheme_dm scheme = new("discovery_mode_TDMA_scheme", number_of_slaves);
		return scheme;
	endfunction	
	
endclass
