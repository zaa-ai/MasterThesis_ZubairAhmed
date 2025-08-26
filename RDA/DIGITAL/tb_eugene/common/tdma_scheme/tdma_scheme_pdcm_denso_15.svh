/**
 * Class: tdma_scheme_pdcm_denso
 * 
 * Valid Denso like TDMA scheme that defined 15 packets.
 */
class tdma_scheme_pdcm_denso_15 extends tdma_scheme_pdcm;

	function new(string name = "pdcm_TDMA_scheme_DENSO_15");
		super.new(name);
		pdcm_period = 2100;
		chiptime = 3;
		add_packet(tdma_scheme_packet_pdcm::new_packet(  30,   70, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet( 165,  205, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet( 300,  340, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet( 435,  475, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet( 570,  610, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet( 705,  745, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet( 840,  880, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet( 975, 1015, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(1110, 1150, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(1245, 1285, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(1380, 1420, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(1515, 1555, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(1650, 1690, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(1785, 1825, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(1920, 1960, 8, dsi3_pkg::SID_8Bit));
		valid = 1'b1;
	endfunction
endclass
