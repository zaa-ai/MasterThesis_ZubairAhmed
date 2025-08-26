/**
 * Class: spi_master_register_seq
 * 
 * Base class for DSI command queue sequences.
 */
class spi_dsi_command_seq extends spi_seq;
	
	rand logic[project_pkg::DSI_CHANNELS-1:0] channel_bits;
	
	`uvm_object_utils_begin(spi_dsi_command_seq)
		`uvm_field_int(channel_bits, UVM_DEFAULT | UVM_BIN)
	`uvm_object_utils_end
	
	function new(string name = "DSI command");
		super.new(name);
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			return {get_command_code(), channel_bits, filler[9:0]};
		end
		return 	super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		channel_bits = data_in[0][CHANNELS_MSB:CHANNELS_LSB];
		return super.create_from(data_in, data_out);
	endfunction
endclass


