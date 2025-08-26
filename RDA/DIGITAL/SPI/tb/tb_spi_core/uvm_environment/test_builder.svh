/*------------------------------------------------------------------------------
 * File          : test_builder.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 20, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

typedef struct {
	data_t	miso;
	data_t	mosi;
	data_t	status_word;
	bit			transmit;
} spi_word_t;

typedef spi_test_seq;

class test_builder;
	
	spi_word_t	words[$];
	data_t		words_for_crc_in[$];
	data_t		words_for_crc_out[$];
	
	function new();
		words.delete();
		words_for_crc_in.delete();
		words_for_crc_out.delete();
	endfunction
	
	function spi_seq get_seq(spi_sequencer sequencer);
		spi_seq	seq;
		logic[15:0]	spi_words[$];
		for (int i=0; i< words.size(); i++)
			spi_words.push_back(words[i].mosi);
		seq = spi_test_seq::create_test_seq_with_words(sequencer, spi_words);
		return seq;
	endfunction
	
	function test_builder add_initial_word(data_t mosi);
		spi_word_t	word;
		word.mosi = mosi;
		word.miso = $urandom_range(16'hffff,0);
		word.status_word = $urandom_range(16'hffff,0);
		word.transmit = 1'b0;
		words_for_crc_in.push_back(mosi);
		words_for_crc_out.push_back(word.miso);
		words.push_back(word);
		return this;
	endfunction
	
	function test_builder add_transmit_word(data_t mosi);
		spi_word_t	word;
		word = create_word(.mosi(mosi), .transmit(1'b1));
		words.push_back(word);
		words_for_crc_in.push_back(mosi);
		words_for_crc_out.push_back(word.miso);
		return this;
	endfunction
	
	function test_builder add_crc_command(data_t mosi, bit crc_correct);
		spi_word_t	word;
		data_t crc_in;
		word = create_word(.mosi(mosi), .transmit(1'b1));
		words.push_back(word);
		word = create_word(.mosi(crc_in), .miso());
		return this;
	endfunction
	
	
	function spi_word_t	create_word(data_t mosi, data_t miso = $urandom_range(16'hffff,0), data_t status_word = $urandom_range(16'hffff,0), bit transmit=1'b0);
		spi_word_t	word;
		word.mosi = mosi;
		word.miso = miso;
		word.status_word = status_word;
		word.transmit = transmit;
		return word;
	endfunction
	
	
endclass