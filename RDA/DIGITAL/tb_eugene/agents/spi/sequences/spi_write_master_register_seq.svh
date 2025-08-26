/**
 * Class: spi_master_register_seq
 * 
 * Write master register sequence.
 */
class spi_write_master_register_seq extends spi_master_register_seq;
	
	`uvm_object_utils(spi_write_master_register_seq)
	
	function new(string name = "write master register");
		super.new(name);
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_REG_WRITE;
	endfunction
		
	virtual function int get_word_count();
		return 2;
	endfunction	
	
	virtual function logic[15:0] get_word(int index);
		if(index == 1) return data;
		return super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(data_in.size() < get_word_count()) begin
			return 0;
		end
		data = data_in[1];
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("write 0x%04h (%s) with 0x%04h",address, addresses_pkg::addresses[address], data);
	endfunction
endclass


