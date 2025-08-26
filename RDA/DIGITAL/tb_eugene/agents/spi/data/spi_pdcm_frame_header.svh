
/**
 * PDCM frame header flags 
 */
typedef enum {
	/**
	 *  packet count error (more packets received than defined by the TDMA scheme)
	 */
	PC=15
	
} pdcm_frame_header_flags;


/**
 * PDCM frame header. Part of a SPI read PDCM frame command.
 */
class spi_pdcm_frame_header extends flags_container #(pdcm_frame_header_flags);
	
	logic[1:0] channel_index;
	logic[7:0] packet_count;
	
	`uvm_object_utils_begin(spi_pdcm_frame_header)
		`uvm_field_int (channel_index, UVM_BIN)
		`uvm_field_int (packet_count, UVM_DEFAULT)
	`uvm_object_utils_end
	
	covergroup cov_spi_pdcm_frame_header;
		option.per_instance = 0;
		cp_pc : coverpoint flags[PC];
		coverpoint channel_index {
			bins channel_0	= {0};
			bins channel_1	= {1};
		}
		coverpoint packet_count {
			bins zero 		= {0};
			bins valid 		= {8'd1, 8'd15};
			bins too_many 	= {8'd16,8'd254};
			bins max   		= {8'd255};
		}
		cross cp_pc, channel_index, packet_count;
	endgroup

	function new(string name = "spi_pdcm_frame_header");
		super.new(name);
		cov_spi_pdcm_frame_header = new();
	endfunction
	
	virtual function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n", "packet_count = %0d\n"}, get_full_name(), packet_count);
		return s;
	endfunction
	
	virtual function void sample_cov();
		cov_spi_pdcm_frame_header.sample();
	endfunction
endclass