/**
 * Class: spi_test_seq
 * 
 * TODO: Add class documentation
 */
class spi_test_seq extends spi_any_command_seq;
	
	static function spi_seq create_test_seq(spi_sequencer_t sequencer, int number_of_words);
		spi_test_seq new_seq = new();
		
		new_seq.set_item_context(null, sequencer);
		
		for (int i=0; i<number_of_words; i++) begin
			new_seq.command_words.push_back($urandom_range(16'hffff));
		end
		
		new_seq.finish_with_csn_active = 1'b0;
		
		return new_seq;
	endfunction
	
	static function spi_seq create_test_seq_with_words(spi_sequencer_t sequencer, logic[15:0] words[$]);
		spi_test_seq new_seq = new();
		new_seq.set_item_context(null, sequencer);
		new_seq.command_words = words;
		new_seq.finish_with_csn_active = 1'b0;
		return new_seq;
	endfunction
	
endclass


