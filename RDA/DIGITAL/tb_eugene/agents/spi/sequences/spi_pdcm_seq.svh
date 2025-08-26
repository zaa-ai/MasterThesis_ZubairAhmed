/**
 * Class: spi_pdcm_seq
 * 
 * Start PDCM.
 */
class spi_pdcm_seq extends spi_dsi_command_seq;
	
	rand logic[7:0] pulse_count;
	
	`uvm_object_utils_begin(spi_pdcm_seq)
		`uvm_field_int(pulse_count, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
	
	constraint co_words	{ pulse_count inside{[0:255]};}
	
	covergroup cov_pdcm;
		option.per_instance = 0;
		coverpoint channel_bits;
		coverpoint pulse_count {
			bins infinite = {8'h0};
			bins few  = {8'h1, 8'hF};
			bins med  = {8'h10, 8'h80};
			bins many = {8'h81, 14'hFF};
		}
		cross pulse_count, channel_bits;
	endgroup
	
	function new(string name = "PDCM Transmit");
		super.new(name);
		cov_pdcm = new();
	endfunction
		
	virtual function void sample_cov();
		super.sample_cov();
		cov_pdcm.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_PDCM;
	endfunction
		
	virtual function int get_word_count();
		return 1;
	endfunction	
	
	virtual function logic[15:0] get_word(int index);
		logic[15:0] cmd = super.get_word(0);
		cmd[7:0] = pulse_count;
		return cmd;
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		pulse_count = data_in[0][7:0];
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("PDCM: channels %04b, pulses %d", channel_bits, pulse_count);
	endfunction
	
endclass
