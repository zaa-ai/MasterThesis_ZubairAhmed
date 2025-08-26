/**
 * Class: spi_sync_dsi_channels_seq
 * 
 * Synchronize DSI channels.
 */
class spi_sync_dsi_channels_seq extends spi_dsi_command_seq;
	
	rand bit external_sync;
	
	`uvm_object_utils_begin(spi_sync_dsi_channels_seq)
		`uvm_field_int(external_sync, UVM_DEFAULT )
	`uvm_object_utils_end
	
	/************************ constraints ************************/
	covergroup cov_sync_channels;
		option.per_instance = 0;
		coverpoint channel_bits;
		coverpoint external_sync;
		cross external_sync, channel_bits;
	endgroup
	
	/************************ Methods declarations ************************/
	function new(string name = "Sync");
		super.new(name);
		cov_sync_channels = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_sync_channels.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_DSI_SYNC;
	endfunction
		
	virtual function int get_word_count();
		return 1;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			logic[15:0] word = super.get_word(0);
			word[0] = external_sync;
			return word;
		end
		return super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		external_sync = data_in[0][0];
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("SYNC: channels %04b, EXTERNAL=%1b", channel_bits, external_sync);
	endfunction
	
endclass