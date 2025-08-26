/**
 * Incomplete spi_read_master_register_seq.
 */
class spi_incomplete_read_master_register_seq extends spi_read_master_register_seq;
		
	rand int word_count;
	
	`uvm_object_utils_begin(spi_incomplete_read_master_register_seq)
		`uvm_field_int(word_count, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
		
	function new(string name = "Incomplete Read Master Register");
		super.new(name);
	endfunction

	virtual function int get_word_count();
		return word_count;
	endfunction	
	
	virtual function string convert2string();
		return $sformatf("incomplete read master register with %0d word", word_count);
	endfunction
endclass


class spi_incomplete_register_reads_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_register_reads_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_register_reads");
	endfunction
	
	virtual task run_tests();
		log_sim_description("send incomplete read master register commands", LOG_LEVEL_SEQUENCE);
		
		repeat(5) begin
			regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
			registers.check_flag(regmodel.SPI.SPI_registers.STATUS_WORD.SCE, 1'b0);
			
			`spi_frame_begin
				`spi_frame_create(spi_incomplete_read_master_register_seq, address == 12'(ADDR_INFO_IC_REVISION); word_count == 1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#10us;
			registers.check_flag(regmodel.SPI.SPI_registers.STATUS_WORD.SCE, 1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_read_status_seq,)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end_with_status('{SCI, NT0, NT1})
			#50us;			
			`create_and_send(spec_CRM_command_seq)
		end
	endtask
endclass

