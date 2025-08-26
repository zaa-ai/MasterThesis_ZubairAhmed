/**
 * Incomplete spi_reset_seq. 
 */
class spi_incomplete_reset_seq extends spi_reset_seq;
		
	rand int word_count;
	
	`uvm_object_utils_begin(spi_incomplete_reset_seq)
		`uvm_field_int(word_count, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
		
	function new(string name = "incomplete reset command");
		super.new(name);
	endfunction
	
	function void post_randomize();
		if(word_count < 4) begin
			incomplete = 1'b1;
			incomplete_word_count = word_count;
			incomplete_last_word = 16'hffff;
		end
	endfunction
	
	virtual function int get_word_count();
		return word_count;
	endfunction	
	
	virtual function string convert2string();
		return $sformatf("incomplete SPI reset with %0d words", word_count);
	endfunction
endclass


class spi_incomplete_reset_command_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_reset_command_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_reset_command");
	endfunction
	
	virtual task run_tests();
		int word_count = 4;
		log_sim_description("perform incomplete SPI reset (too few words)", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		// invalidate any existing TDMA scheme
		`spi_frame_begin
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;

		for (int i = 1; i < word_count; i++) begin
		
			log_sim_description($sformatf("perform incomplete SPI reset with %0d of %0d words", i, word_count), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_incomplete_reset_seq, word_count == local::i;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			
			transaction_recorder.expect_tr_count_for_all_channels(1);
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end_with_status({NT0, NT1, CR0, CR1})
			#50us;
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
		transaction_recorder.disable_recorder();
	endtask
endclass