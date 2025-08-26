/**
 * Class: tdma_scheme_packet_dm
 * 
 * Discovery Mode TDMA scheme information for a packet send by a slave
 */
class tdma_scheme_packet_dm extends tdma_scheme_packet;
	
	`uvm_object_utils (tdma_scheme_packet_dm)
	
	function new(string name="tdma_scheme_packet_dm");
		super.new(name);
		begin
			dsi3_packet dm_packet = new();
			packet = dm_packet;
		end
	endfunction
	
	static function tdma_scheme_packet_dm new_packet(
			shortint unsigned earliest_start, 
			shortint unsigned latest_start,
			int unsigned symbols, 
			real tolerance_min=0.95, 
			real tolerance_max=1.05);
		
		tdma_scheme_packet_dm packet = new();
		packet.set_packet_values(earliest_start, latest_start, symbols, dsi3_pkg::SID_0Bit, tolerance_min, tolerance_max);
		return packet;
	endfunction
endclass
