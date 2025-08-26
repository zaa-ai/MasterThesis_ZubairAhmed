/**
 * Class: tdma_scheme_packet_pdcm
 * 
 * PDCM TDMA scheme information for a packet send by a slave
 */
class tdma_scheme_packet_pdcm extends tdma_scheme_packet;
	
	`uvm_object_utils (tdma_scheme_packet_pdcm)
	
	function new(string name="tdma_scheme_packet_pdcm", dsi3_pkg::sid_length_e id_symbols = dsi3_pkg::SID_8Bit);
		super.new(name);
		begin
			dsi3_pdcm_packet pdcm_packet = new();
			pdcm_packet.source_id_symbols = id_symbols;
			packet = pdcm_packet;
		end
	endfunction
	
	// make sure that the contained dsi3_pdcm_packet has the same SID as defined in this tdma_scheme_packet	
	function void post_randomize();
		dsi3_pdcm_packet pdcm_packet;
		if($cast(pdcm_packet, packet) == 1) begin
			pdcm_packet.source_id_symbols = id_symbol_count;
		end
	endfunction
	
	static function tdma_scheme_packet_pdcm new_packet(
			shortint unsigned earliest_start, 
			shortint unsigned latest_start,
			int unsigned symbols, 
			dsi3_pkg::sid_length_e id_symbols, 
			real tolerance_min=0.95, 
			real tolerance_max=1.05,
			error_injection_e crc_error_injection = RANDOM_ERROR, 
			error_injection_e symbol_coding_error_injection = NEVER_ERROR, 
			error_injection_e chip_length_error_injection = NEVER_ERROR);
		
		tdma_scheme_packet_pdcm packet = new("tdma_scheme_packet_pdcm", id_symbols);
		packet.set_packet_values(earliest_start, latest_start, symbols, id_symbols, tolerance_min, tolerance_max, crc_error_injection, symbol_coding_error_injection, chip_length_error_injection);
		return packet;
	endfunction
	
endclass
