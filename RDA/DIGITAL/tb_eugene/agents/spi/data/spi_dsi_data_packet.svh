
/**
 * DSI packet / DSI response error bits 
 */
typedef enum {
	/**
	 * symbol count error (received unexpected number of symbols or more than 255 symbols)
	 */
	SCE=13,
	/**
	 * CRC error (CRC of the received data was incorrect or no data has been received or data has been received incompletely)
	 */
	CRC=12, 
	/**
	 * timing error (too early or too late slave response in CRM or PDCM)
	 */
	TE=11,
	/**
	 * symbol coding error
	 */
	SE=10, 
	/**
	 * voltage error at DSI pin
	 */
	VE=9,
	/**
	 * CE CLKREF error 
     *  • CLKREF signal is missing, or 
     *  • CLKREF frequency is out of the recommended range 
	 */
	CE=8
	} dsi_response_flags;


/**
 * A DSI response data packet. Part of a SPI read data packet command.
 */
class spi_dsi_data_packet extends flags_container #(dsi_response_flags);
	
	logic[1:0]  channel_index;
	logic[7:0]  symbol_count;
	logic[15:0] data[$];
	
	`uvm_object_utils_begin(spi_dsi_data_packet)
		`uvm_field_int (channel_index, UVM_BIN)
		`uvm_field_int (symbol_count, UVM_DEFAULT)
		`uvm_field_queue_int (data, UVM_DEFAULT)
	`uvm_object_utils_end
	
	covergroup cov_spi_dsi_data_packet;
		option.per_instance = 0;
		coverpoint flags[SCE];
		coverpoint flags[CRC];
		coverpoint flags[TE];
		coverpoint flags[SE];
		coverpoint flags[VE];
		coverpoint flags[CE];
		coverpoint channel_index {
			bins channel_0	= {0};
			bins channel_1	= {1};
		}
		coverpoint symbol_count;
	endgroup
	
	/************************ Methods declarations ************************/
	function new(string name = "spi_dsi_data_packet");
		super.new(name);
		cov_spi_dsi_data_packet = new();
	endfunction
	
	virtual function void sample_cov();
		cov_spi_dsi_data_packet.sample();
	endfunction
	
	virtual function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n", "symbol_count = %0d\n"}, get_full_name(), symbol_count);
		return s;
	endfunction
	
	static function spi_dsi_data_packet create_packet(logic[1:0] channel_index, byte symbol_count, logic[15:0] data[$], dsi_response_flags flags[$]);
		spi_dsi_data_packet	packet = new();
		packet.data = data;
		packet.symbol_count = symbol_count;
		packet.channel_index = channel_index;
		packet.set_flags(flags);
		return packet;
	endfunction
	
endclass