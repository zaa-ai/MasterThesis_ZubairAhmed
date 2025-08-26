/**
 * Class: spi_master_register_seq
 * 
 * Base class for sequences that access master registers.
 */
class spi_master_register_seq extends spi_seq;
	
	rand logic[11:0] address;
	rand logic[15:0] data;
	
	`uvm_object_utils_begin(spi_master_register_seq)
		`uvm_field_int(address, UVM_DEFAULT | UVM_HEX)
		`uvm_field_int(data, UVM_DEFAULT | UVM_HEX)	
	`uvm_object_utils_end
	
	/************************ constraints ************************/
	constraint co_address	{ address inside{[0:4095]};} 
	
	/************************ Methods declarations ************************/
	function new(string name = "master register access");
		super.new(name);
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) return {get_command_code(), address};
		return 	super.get_word(index);
	endfunction

	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		address = data_in[0][11:0];
		return super.create_from(data_in, data_out);
	endfunction
	
endclass


