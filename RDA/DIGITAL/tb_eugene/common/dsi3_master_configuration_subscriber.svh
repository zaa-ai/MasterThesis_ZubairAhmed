/**
 * Class: dsi3_master_configuration_subscriber
 * 
 * Subscribes to a DSI3 master bit time broadcast for configuration purposes 
 */
class dsi3_master_configuration_subscriber extends uvm_subscriber #(dsi3_master_configuration_tr);

	dsi3_pkg::dsi3_bit_time_e bit_time;
	int chip_time;
	
	bit crc_en;
	bit sync_pdcm;
	bit sync_master;
	int tx_shift;
	
	int crm_time;
	int crm_time_nr;
	
	`uvm_component_utils_begin (dsi3_master_configuration_subscriber)
		`uvm_field_enum(dsi3_pkg::dsi3_bit_time_e, bit_time, UVM_DEFAULT)
		`uvm_field_int(chip_time, 	UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(crc_en,	 	UVM_DEFAULT | UVM_BIN)
		`uvm_field_int(sync_pdcm, 	UVM_DEFAULT | UVM_BIN)
		`uvm_field_int(sync_master, UVM_DEFAULT | UVM_BIN)
		`uvm_field_int(tx_shift, 	UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(crm_time, 	UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(crm_time_nr,	UVM_DEFAULT | UVM_DEC)
	`uvm_component_utils_end
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	virtual function void write(dsi3_master_configuration_tr t);
		bit_time = t.bit_time;
		chip_time = t.chip_time;
		crc_en = t.crc_en;
		sync_pdcm = t.sync_pdcm;
		sync_master = t.sync_master;
		tx_shift = t.tx_shift_value;
		crm_time = t.crm_time;
		crm_time_nr = t.crm_time_nr;
	endfunction
	
	virtual function dsi3_pkg::dsi3_bit_time_e get_bit_time();
		return bit_time;
	endfunction
	
	virtual function int get_chip_time();
		return chip_time;
	endfunction
	
	virtual function int get_tx_shift();
		return tx_shift;
	endfunction
	
	virtual function bit is_crc_en();
		return crc_en;
	endfunction

	virtual function bit is_sync_pdcm();
		return sync_pdcm;
	endfunction
	
	virtual function bit is_sync_master();
		return sync_master;
	endfunction
	
	virtual function int get_crm_time();
		return crm_time;
	endfunction
	
	virtual function int get_crm_time_nr();
		return crm_time_nr;
	endfunction
endclass
