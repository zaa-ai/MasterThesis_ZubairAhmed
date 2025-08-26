/**
 * Class: spi_validate_tdma_scheme_seq
 * 
 * Validate all uploaded TDMA packets and set PDCM period.
 */
class spi_validate_tdma_scheme_seq extends spi_dsi_command_seq;
	
	rand logic[15:0] pdcm_period;
	rand logic[3:0] packet_count;
	
	`uvm_object_utils_begin(spi_validate_tdma_scheme_seq)
		`uvm_field_int(pdcm_period, UVM_DEFAULT | UVM_HEX)
		`uvm_field_int(packet_count, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
	
	covergroup cov_validate_tdma;
		option.per_instance = 0;
		coverpoint channel_bits;
		coverpoint packet_count;
		coverpoint pdcm_period {
			bins minimum = {16'h0,    16'd100};
			bins normal  = {16'd101,  16'd5000};
			bins med	 = {16'd5001, 16'hFFEF};
			bins maximum = {16'hFFF0, 16'hFFFF};
		}
		cross packet_count, channel_bits;
	endgroup
	
	/************************ Methods declarations ************************/
	function new(string name = "Validate TDMA Scheme");
		super.new(name);
		cov_validate_tdma = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_validate_tdma.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_UPLOAD_TDMA;
	endfunction
		
	virtual function int get_word_count();
		return 2;
	endfunction	
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			logic[15:0] cmd = super.get_word(0);
			cmd[5] = 1'b0;
			cmd[3:0] = packet_count;
			return cmd;
		end
		if(index == 1) return pdcm_period;
		return super.get_word(index);
	endfunction
	
	virtual function bit starts_with(logic[15:0] word);
		return super.starts_with(word) && word[5] == 1'b0;
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(data_in.size() < get_word_count()) begin
			return 0;
		end 
		if(data_in[0][5] != 1'b0) return 1'b0;
		packet_count = data_in[0][3:0];
		pdcm_period = data_in[1];
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("Validate TDMA Scheme of %0d packets for channels %02b", packet_count, channel_bits);
	endfunction
	
endclass


