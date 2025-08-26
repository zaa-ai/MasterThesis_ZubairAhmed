/**
 * Class: tdma_scheme_crm
 * 
 * TDMA scheme for CRM transmissions
 */
class tdma_scheme_crm extends tdma_scheme;

	function new(string name = "tdma_scheme_crm");
		super.new(name);
	endfunction
	
	virtual function tdma_scheme_packet create_packet();
		tdma_scheme_packet_crm packet = new();
		return packet;
	endfunction
	
	static function tdma_scheme_crm default_scheme(int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		tdma_scheme_crm scheme = new("crm_scheme");
		scheme.chiptime = chiptime;
		scheme.bit_time = bit_time;
		scheme.add_packet(tdma_scheme_packet_crm::new_packet(265 * (bit_time/8), 340 * (bit_time/8), 8, $urandom_range(1050, 950)/1000.0));
		return scheme;
	endfunction		
	
	static function tdma_scheme valid(int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		tdma_scheme scheme = new("crm_valid_scheme");
		scheme.chiptime = chiptime;
		scheme.bit_time =  bit_time;
		scheme.add_packet(tdma_scheme_packet_crm::get_valid_packet(scheme.bit_time));
		return scheme;
	endfunction	
	
	static function tdma_scheme valid_with_data(logic[15:0] high_word, logic[15:0] low_word, int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
		tdma_scheme scheme = new("crm_valid_scheme");
		scheme.chiptime = chiptime;
		scheme.bit_time =  bit_time;
		add_crm_packet(scheme, high_word, low_word);
		return scheme;
	endfunction
	
	static function void add_crm_packet(tdma_scheme scheme, logic[15:0] high_word, logic[15:0] low_word);
		logic[3:0] data[$];
		tdma_scheme_packet tdma_packet = tdma_scheme_packet_crm::get_valid_packet(scheme.bit_time);
		if (convert_queue#(16, 4)::convert({high_word, low_word}, data)) `uvm_error("tdma_scheme_crm", $sformatf("high/low word data queue could not be properly converted"))
		tdma_packet.packet.data = data;
		scheme.add_packet(tdma_packet);
	endfunction
	
	static function tdma_scheme no_answer();
		tdma_scheme_packet tdma_packet;
		tdma_scheme scheme = new("crm_no_answer");
		scheme.chiptime = 3;
		scheme.bit_time =  dsi3_pkg::BITTIME_8US;
		
		tdma_packet = tdma_scheme_packet_crm::get_valid_packet(scheme.bit_time);
		tdma_packet.enable = 1'b0;
		scheme.add_packet(tdma_packet);
		return scheme;
	endfunction
    
    static function tdma_scheme paket_with_SCE_error(logic[3:0] data[$], int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
        tdma_scheme_packet tdma_packet;
        tdma_scheme scheme = new("crm_scheme_with_SCE_error");
        scheme.chiptime = chiptime;
        scheme.bit_time =  bit_time;
        
        tdma_packet = tdma_scheme_packet_crm::get_valid_packet(scheme.bit_time);
        tdma_packet.packet.data = data;
        scheme.add_packet(tdma_packet);
        return scheme;
    endfunction 
    
    static function tdma_scheme paket_with_SE_error(logic[15:0] high_word, logic[15:0] low_word, int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
        logic[3:0] data[$];
        tdma_scheme_packet tdma_packet;
        tdma_scheme scheme = new("crm_scheme_with_SE_error");
        scheme.chiptime = chiptime;
        scheme.bit_time =  bit_time;
        
        tdma_packet = tdma_scheme_packet_crm::get_valid_packet(scheme.bit_time);
        tdma_packet.symbol_coding_error_injection = ALWAYS_ERROR;//RANDOM_ERROR
       
        if (convert_queue#(16, 4)::convert({high_word, low_word}, data)) `uvm_error("tdms_scheme_crm", $sformatf("high/low word data queue could not be properly converted"))
        tdma_packet.packet.data = data;
        scheme.add_packet(tdma_packet); 

        return scheme;
    endfunction 
    
    static function tdma_scheme paket_with_CRC_error(logic[15:0] high_word, logic[15:0] low_word, int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
    	logic[3:0] data[$];
    	tdma_scheme_packet tdma_packet;
    	tdma_scheme scheme = new("crm_scheme_with_SE_error");
    	scheme.chiptime = chiptime;
    	scheme.bit_time =  bit_time;
        
    	tdma_packet = tdma_scheme_packet_crm::get_valid_packet(scheme.bit_time);
    	tdma_packet.crc_error_injection = ALWAYS_ERROR;//RANDOM_ERROR
        
    	if (convert_queue#(16, 4)::convert({high_word, low_word}, data)) `uvm_error("tdms_scheme_crm", $sformatf("high/low word data queue could not be properly converted"))
    	tdma_packet.packet.data = data;
    	scheme.add_packet(tdma_packet); 

    	return scheme;
    endfunction 
endclass
