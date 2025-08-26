/**
 * Class: spi_clear_dsi_data_buffers_seq
 * 
 * Remove all data from DSI buffers.
 */
class spi_clear_dsi_data_buffers_seq extends spi_dsi_command_seq;
	
	rand bit crm_buffer;
	rand bit pdcm_buffer;
	
	`uvm_object_utils_begin(spi_clear_dsi_data_buffers_seq)
		`uvm_field_int (crm_buffer, UVM_DEFAULT)
		`uvm_field_int (pdcm_buffer, UVM_DEFAULT)
	`uvm_object_utils_end
	
	covergroup cov_clear_data_buffer;
		option.per_instance = 0;
		coverpoint channel_bits;
		coverpoint crm_buffer;	
		coverpoint pdcm_buffer;
		cross crm_buffer, pdcm_buffer, channel_bits;
	endgroup
	
	/************************ Methods declarations ************************/
	function new(string name = "clear DSI data buffers");
		super.new(name);
		cov_clear_data_buffer = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_clear_data_buffer.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_DSI_CLEAR_BUF;
	endfunction
		
	virtual function int get_word_count();
		return 1;
	endfunction	
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			logic[15:0] word = super.get_word(0);
			word[0] = crm_buffer;
			word[1] = pdcm_buffer;
			return word;
		end
		return super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(data_in.size() < get_word_count()) begin
			return 0;
		end 
		crm_buffer = data_in[0][0];
		pdcm_buffer = data_in[0][1];
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("clear DSI data buffers for channels %02b", channel_bits);
	endfunction
	
endclass