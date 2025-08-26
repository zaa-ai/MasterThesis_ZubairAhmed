/**
 * Class: spi_discovery_mode_seq
 * 
 * Start discovery mode.
 */
class spi_discovery_mode_seq extends spi_dsi_command_seq;
	
	`uvm_object_utils(spi_discovery_mode_seq)
	
	/************************ constraints ************************/
	
	/************************ Methods declarations ************************/
	function new(string name = "start DSI discovery mode");
		super.new(name);
		cov_discovery_mode = new();
	endfunction
	
	covergroup cov_discovery_mode;
		option.per_instance = 0;
		coverpoint channel_bits;
	endgroup
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_discovery_mode.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_DSI_DISCOVERY_MODE;
	endfunction
		
	virtual function int get_word_count();
		return 1;
	endfunction	
	
	virtual function string convert2string();
		return $sformatf("start DSI discovery mode for channels %02b", channel_bits);
	endfunction
	
endclass