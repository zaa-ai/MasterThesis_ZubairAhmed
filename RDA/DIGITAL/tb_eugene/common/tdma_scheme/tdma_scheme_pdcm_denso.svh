/**
 * Class: tdma_scheme_pdcm_denso
 * 
 * Valid TDMA scheme from Denso.
 */
class tdma_scheme_pdcm_denso extends tdma_scheme_pdcm;

	function new(string name = "pdcm_TDMA_scheme_DENSO");
		super.new(name);
		pdcm_period = 1000;
		chiptime = 3;
		add_packet(tdma_scheme_packet_pdcm::new_packet( 30,  70, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(165, 205, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(300, 340, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(435, 475, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(570, 610, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(705, 745, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(840, 880, 8, dsi3_pkg::SID_8Bit));
        valid = 1'b1;
	endfunction
	
endclass
