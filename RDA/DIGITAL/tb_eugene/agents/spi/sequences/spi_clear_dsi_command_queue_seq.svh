/**
 * Class: spi_clear_dsi_command_queue_seq
 * 
 * Remove all commands from DSI command queue.
 */
class spi_clear_dsi_command_queue_seq extends spi_dsi_command_seq;
	
	`uvm_object_utils(spi_clear_dsi_command_queue_seq)
	
	/************************ constraints ************************/
	
	/************************ Methods declarations ************************/
	function new(string name = "clear DSI command queue");
		super.new(name);
		cov_clear_dsi_queue = new();
	endfunction
	
	covergroup cov_clear_dsi_queue;
		option.per_instance = 0;
		coverpoint channel_bits;
	endgroup
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_clear_dsi_queue.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_DSI_CLEAR_QUEUE;
	endfunction
		
	virtual function int get_word_count();
		return 1;
	endfunction	
	
	virtual function string convert2string();
		return $sformatf("clear DSI command queue for channels %02b", channel_bits);
	endfunction
	
endclass
