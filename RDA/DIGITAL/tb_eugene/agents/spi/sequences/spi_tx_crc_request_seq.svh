/**
 * Class: spi_master_register_seq
 * 
 * SPI frame CRC command sequence.
 */
class spi_tx_crc_request_seq extends spi_seq;
	
	logic mosi_crc_enable; 	 		// sets whether a mosi CRC will be calculated automatically for a command frame
	rand logic mosi_crc_correct; 	// sets whether a correct or a wrong CRC will be sent to IC
	rand logic[15:0] mosi_crc; 		// CRC to be sent from host to IC (this CRC is calculated within spi_command_frame)

	logic miso_crc_correct; 		// information flag whether a correct CRC has been received from IC
	logic[15:0] miso_crc; 			// CRC that has been received from IC 
	
	`uvm_object_utils_begin (spi_tx_crc_request_seq)
		`uvm_field_int(mosi_crc_correct, UVM_DEFAULT)
		`uvm_field_int(mosi_crc, UVM_DEFAULT | UVM_HEX)
		`uvm_field_int(miso_crc_correct, UVM_DEFAULT)
		`uvm_field_int(miso_crc, UVM_DEFAULT | UVM_HEX)
	`uvm_object_utils_end
	
		
	/************************ constraints ************************/
	constraint co_weight_crc_correct { mosi_crc_correct dist {0 := 1, 1:= 5}; };
	
	covergroup cov_tx_crc;
		option.per_instance = 0;
		coverpoint mosi_crc_correct {
			bins not_correct = {0};
			bins correct = {1};
		}
	endgroup	
		
	/************************ Methods declarations ************************/
	function new(string name = "SPI Frame CRC Request");
		super.new(name);
		mosi_crc_enable = 1;
		cov_tx_crc = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_tx_crc.sample();
	endfunction		
		
	virtual function spi_cmd_type get_command_code();
		return CMD_TX_CRC;
	endfunction
	
	virtual function int get_word_count();
		return 2;
	endfunction	
	
	virtual function spi_mirroring_type get_mirroring_type();
		return spi_pkg::NONE;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		if(index == 1) return mosi_crc;
		return super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(data_in.size() < get_word_count()) begin
			return 0;
		end 
		mosi_crc = data_in[1];
		miso_crc = data_out[1];
		return super.create_from(data_in, data_out);
	endfunction
		
	virtual function string convert2string();
		return $sformatf("CRC Request, MOSI: 0x%04h, MISO: 0x%04h", mosi_crc, miso_crc);
	endfunction
			
endclass


