/**
 * Incomplete spi_read_pdcm_frame_seq. 
 */
class spi_incomplete_read_pdcm_frame_seq extends spi_read_pdcm_frame_seq;
		
	rand int word_count;
	
	`uvm_object_utils_begin(spi_incomplete_read_pdcm_frame_seq)
		`uvm_field_int(word_count, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
		
	function new(string name = "incomplete read PDCM frame");
		super.new(name);
	endfunction

	virtual function int get_word_count();
		return word_count;
	endfunction	
	
	virtual function string convert2string();
		return $sformatf("incomplete read PDCM frame with %0d word: channels 0b%02b", word_count, channel_bits);
	endfunction
endclass


class spi_incomplete_read_pdcm_denso_15_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_read_pdcm_denso_15_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_read_pdcm_denso_15");
	endfunction : new
	
	virtual task run_tests();
		tdma_scheme_pdcm_denso_15 scheme = new();
		int word_count;
		
		log_sim_description("perform incomplete read PDCM commands (too few words) with Denso like TDMA scheme of 15 packets", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		word_count = spi_read_pdcm_frame_seq::calculate_word_count(2'b11);
		
		for (int i = 1; i < word_count; i++) begin
			log_sim_description($sformatf("perform incomplete read PDCM with %0d of %0d words in command", i, word_count), LOG_LEVEL_OTHERS);
			regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd2;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
			`spi_frame_end
			
			#(2 * scheme.pdcm_period * 1us);
			`spi_frame_begin
				`spi_frame_create(spi_incomplete_read_pdcm_frame_seq, channel_bits == 2'b11; word_count == local::i;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#10us;
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
	endtask
endclass
