/**
 * Class: spi_any_command_seq
 * 
 * SPI commands that consists of a given queue of words (can represent any command or uncomplete commands, ...).
 */
class spi_any_command_seq extends spi_seq;
	
	logic[15:0] command_words[$];
	spi_mirroring_type mirroring_type = spi_pkg::ALL_WORDS;
	
	`uvm_object_utils_begin (spi_any_command_seq)
	`uvm_object_utils_end
		
	/************************ constraints ************************/
		
	/************************ Methods declarations ************************/
	function new(string name = "SPI any command");
		super.new(name);
	endfunction
	
	virtual function int get_word_count();
		return command_words.size();
	endfunction	
	
	virtual function spi_mirroring_type get_mirroring_type();
		return mirroring_type;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		return command_words[index];
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		return 0;
	endfunction
		
	virtual function string convert2string();
		return $sformatf("any command");
	endfunction
			
endclass


