/**
 * Class: tdma_scheme_packet_crm
 * 
 * CRM TDMA scheme information for a packet send by a slave
 */
class tdma_scheme_packet_crm extends tdma_scheme_packet;
	
	`uvm_object_utils (tdma_scheme_packet_crm)
	
	function new(string name="tdma_scheme_packet_crm");
		super.new(name);
		begin
			dsi3_crm_packet crm_packet = new();
			packet = crm_packet;
		end
	endfunction
	
	static function tdma_scheme_packet_crm new_packet(
			shortint unsigned earliest_start, 
			shortint unsigned latest_start,
			int unsigned symbols, 
			real tolerance_min=0.95, 
			real tolerance_max=1.05,
			error_injection_e crc_error_injection = RANDOM_ERROR, 
			error_injection_e symbol_coding_error_injection = NEVER_ERROR, 
			error_injection_e chip_length_error_injection = NEVER_ERROR);
		
		tdma_scheme_packet_crm packet = new();
		packet.set_packet_values(earliest_start, latest_start, symbols, dsi3_pkg::SID_0Bit, tolerance_min, tolerance_max, crc_error_injection, symbol_coding_error_injection, chip_length_error_injection);
		return packet;
	endfunction
	
	static function tdma_scheme_packet get_valid_packet(dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		int bit_time_int = dsi3_pkg::get_bit_time(bit_time);
		tdma_scheme_packet packet = new_packet(280*(bit_time_int/8), 310*(bit_time_int/8), 8);
		return packet; 
	endfunction
	
endclass
