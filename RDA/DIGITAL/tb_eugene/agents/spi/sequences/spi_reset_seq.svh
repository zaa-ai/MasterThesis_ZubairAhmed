/**
 * Class: spi_reset_seq
 *
 * Sequence for resetting SPI and it's command queue.
 */
class spi_reset_seq extends spi_seq;
	
	// last bit of last word is a don't care bit
	rand bit last_bit;
	
	// indicates that this read command was incomplete (less words that needed)
	bit incomplete = 1'b0;
	// gets number of words in case of an incomplete read command
	int incomplete_word_count = 0;
	logic[15:0] incomplete_last_word;
	
	`uvm_object_utils_begin(spi_reset_seq)
		`uvm_field_int (last_bit, UVM_DEFAULT)
	`uvm_object_utils_end
	
	/************************ Methods declarations ************************/
	function new(string name = "Reset");
		super.new(name);
	endfunction
	
	virtual function void sample_cov();
		// nothing to sample here
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_RESET;
	endfunction
	
	virtual function int get_word_count();
		return (incomplete == 1'b1) ? incomplete_word_count : 4;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		logic[15:0] word;
		word = 16'hFFFF;
		
		if(incomplete == 1'b1 && index == incomplete_word_count-1) begin
			return incomplete_last_word;
		end
		if(index == 3) begin
			word[0] = last_bit;
		end
		return word;
	endfunction
	
	virtual function string convert2string();
		return $sformatf("Reset SPI");
	endfunction
	
	virtual function bit create_from(logic [15:0] data_in[$], logic [15:0] data_out[$]);
		this.data_in.delete();
		this.data_out.delete();
		
		for (int i = 0; i < data_in.size(); i++) begin
			// copy in/out words
			this.data_in.push_back(data_in[i]);
			this.data_out.push_back(data_out[i]);
			
			if(i < 3 && i < (data_in.size()-1) && data_in[i+1][15:12] != CMD_RESET) begin
				incomplete = 1'b1;
				incomplete_word_count = i+1;
				incomplete_last_word = data_in[i];
				return 1'b1;
			end
			if(data_in[i][15:1] != 15'h7FFF) begin
				incomplete = 1'b1;
				incomplete_word_count = i+1;
				incomplete_last_word = data_in[i];
				return 1'b1;
			end
			if(i == 3) begin
				last_bit = data_in[3][0];
				return 1'b1;
			end
		end
		return 1'b0;
	endfunction
	
endclass


