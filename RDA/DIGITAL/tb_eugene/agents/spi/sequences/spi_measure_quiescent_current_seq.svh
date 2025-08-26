/**
 * Class: spi_measure_quiescent_current_seq
 * 
 * Start measure quiescent current to adopt receiver thresholds.
 */
class spi_measure_quiescent_current_seq extends spi_dsi_command_seq;
	
	`uvm_object_utils(spi_measure_quiescent_current_seq)
	
	function new(string name = "measure quiescent current");
		super.new(name);
		cov_measure_current = new();
	endfunction
	
	covergroup cov_measure_current;
		option.per_instance = 0;
		coverpoint channel_bits;
	endgroup
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_measure_current.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_MEASURE_CURRENT;
	endfunction
		
	virtual function int get_word_count();
		return 1;
	endfunction	
	
	virtual function string convert2string();
		return $sformatf("start measure quiescent current for channels %02b", channel_bits);
	endfunction
	
endclass