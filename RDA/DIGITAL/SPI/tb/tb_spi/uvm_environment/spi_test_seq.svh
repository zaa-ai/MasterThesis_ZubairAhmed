/**
 * Class: spi_test_seq
 * 
 * TODO: Add class documentation
 */
class spi_test_seq extends spi_seq;
	
	static function spi_command_frame_seq create_test_seq(spi_sequencer_t sequencer, int number_of_commands=-1);
		spi_command_frame_seq new_seq = new();
		
		new_seq = spi_frame_factory::create_random_frame(sequencer, number_of_commands);
		return new_seq;
	endfunction
	
	static function spi_command_frame_seq create_test_frame(spi_sequencer_t sequencer, int number_of_commands=-1);
		spi_command_frame_seq new_seq = new();
		
		new_seq = spi_frame_factory::create_random_frame(sequencer, number_of_commands);
		return new_seq;
	endfunction
	
	static function void append_crc_command(spi_command_frame_seq frame);
		spi_frame_factory::append_crc_command(frame);
	endfunction
	
	static function void append_crc_command_with(bit crc_correct, spi_command_frame_seq frame);
		spi_tx_crc_request_seq	crc_seq;
		crc_seq = spi_seq_factory#(spi_tx_crc_request_seq)::create_seq();
		void'(crc_seq.randomize with {mosi_crc_correct == local::crc_correct;});
		frame.add_command(crc_seq);
	endfunction
	
	static function spi_command_frame_seq create_register_read(spi_sequencer_t sequencer, int number_of_reads);
		spi_command_frame_seq new_seq = new();
		
		new_seq = spi_frame_factory::create_read_register_frame(sequencer, number_of_reads);
		return new_seq;
	endfunction
	
	virtual function spi_tr create_transaction(spi_sequencer_t sequencer);
		`uvm_create_on (req, sequencer)
		return req;
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return spi_cmd_type'(0);
	endfunction
	
	virtual function int get_word_count();
		return 0;
	endfunction
	
	virtual function logic[15:0] get_word(int index); 
		return 0;
	endfunction
	
endclass


