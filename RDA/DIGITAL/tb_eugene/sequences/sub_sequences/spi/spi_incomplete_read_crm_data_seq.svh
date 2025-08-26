/**
 * Incomplete spi_read_crm_data_packets_seq. 
 */
class spi_incomplete_read_crm_data_packets_seq extends spi_read_crm_data_packets_seq;
		
	rand int word_count;
	
	`uvm_object_utils_begin(spi_incomplete_read_crm_data_packets_seq)
		`uvm_field_int(word_count, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
		
	function new(string name = "incomplete read CRM data");
		super.new(name);
	endfunction

	virtual function int get_word_count();
		return word_count;
	endfunction	
	
	virtual function string convert2string();
		return $sformatf("incomplete read CRM data with %0d word: channels 0b%02b", word_count, channel_bits);
	endfunction
endclass


class spi_incomplete_read_crm_data_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_read_crm_data_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_read_crm_data");
	endfunction
	
	virtual task run_tests();
		log_sim_description("perform incomplete read CRM commands (too few words) on each channel", LOG_LEVEL_SEQUENCE);

		for (int channels=0; channels < 2 ** project_pkg::DSI_CHANNELS; channels++) begin
			int word_count = spi_read_crm_data_packets_seq::calculate_word_count(2'(channels));
			for (int i = 1; i < word_count; i++) begin
			
				log_sim_description($sformatf("perform incomplete read CRM data with %0d of %0d words at channel 0b%0b", i, word_count, channels), LOG_LEVEL_OTHERS);
				
				`spi_frame_begin
					`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#50us;				
				
				regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
				registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
				check_dab(1'b1);
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'(channels); broad_cast == 1'b0;)
					`spi_frame_create(spi_crm_seq, channel_bits == 2'(channels); broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#1ms;
				check_dab(1'b0);
				`spi_frame_begin
					`spi_frame_create(spi_incomplete_read_crm_data_packets_seq, channel_bits == 2'(channels); word_count == local::i;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b1);
				check_dab(1'b0);
				`spi_frame_begin
					`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'(channels); )
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				if(channels < 'b11 || i > 2) begin
					check_dab(1'b1);
				end
				#50us;
			end
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
	endtask
endclass