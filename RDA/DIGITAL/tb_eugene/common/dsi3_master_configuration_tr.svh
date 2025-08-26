/**
 * Class: dsi3_master_configuration_tr
 *
 * Transaction for broadcasting bit time changes
 */
class dsi3_master_configuration_tr extends uvm_transaction;
	
	bit[project_pkg::DSI_CHANNELS-1:0] dsi_enable;
	
	dsi3_pkg::dsi3_bit_time_e	bit_time;
	int 						chip_time;
	bit 						crc_en;
	bit 						sync_pdcm;
	bit 						sync_master;
	int 						tx_shift_value;
	int							crm_time;
	int 						crm_time_nr;
	
	`uvm_object_utils_begin(dsi3_master_configuration_tr)
		`uvm_field_enum(dsi3_pkg::dsi3_bit_time_e, bit_time, UVM_DEFAULT)
		`uvm_field_int(dsi_enable, UVM_DEFAULT | UVM_BIN)
		`uvm_field_int(chip_time, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(crc_en, UVM_BIN)
		`uvm_field_int(sync_pdcm, UVM_BIN)
		`uvm_field_int(sync_master, UVM_BIN)
		`uvm_field_int(tx_shift_value, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(crm_time, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(crm_time_nr, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
	
	protected function new(string name = "");
		super.new(name);
	endfunction
	
	static function dsi3_master_configuration_tr create_transaction();
		dsi3_master_configuration_tr new_tr = new("master_configuration");
		new_tr.begin_tr($time());
		new_tr.end_tr($time());
		return new_tr;
	endfunction
	
endclass
