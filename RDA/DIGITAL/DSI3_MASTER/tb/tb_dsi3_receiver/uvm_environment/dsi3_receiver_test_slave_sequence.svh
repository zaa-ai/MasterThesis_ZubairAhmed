/**
 * Class: dsi3_receiver_test_slave_sequence
 * 
 * TODO: Add class documentation
 */
class dsi3_receiver_test_slave_sequence extends dsi3_slave_seq;
	
	static function dsi3_slave_seq create_test_seq(dsi3_slave_sequencer_t sequencer, int symbol_count = 8, int chiptime = 2, int tolerance_int = 1000, common_env_pkg::error_injection_e coding_errors = common_env_pkg::NEVER_ERROR);
		dsi3_slave_seq new_seq = new();
		dsi3_slave_tr new_tr;
		
		new_seq.set_item_context(null, sequencer);
		new_tr = new_seq.create_transaction(sequencer);
		
		new_tr.randomize with {
				msg_type == dsi3_pkg::PDCM;
				tolerance_int == local::tolerance_int;
				data.size() == local::symbol_count;
				chiptime == local::chiptime;
				chips_per_symbol == 3;
				symbol_coding_error_injection == local::coding_errors;
				chip_length_error_injection == NEVER_ERROR;
			};		
		new_seq = dsi3_slave_seq::create_seq(new_tr);
		return new_seq;
	endfunction
	
	static function dsi3_slave_seq create_test_seq_with_data(dsi3_slave_sequencer_t sequencer, l4_queue data, int chiptime=2);
		dsi3_slave_seq new_seq = new();
		dsi3_slave_tr new_tr;
		
		new_seq.set_item_context(null, sequencer);
		new_tr = new_seq.create_transaction(sequencer);
		
		new_tr.randomize with {
				msg_type == dsi3_pkg::PDCM;
				tolerance_int == 1000;
				data.size() == local::data.size();
				chiptime == local::chiptime;
				chips_per_symbol == 3;
				symbol_coding_error_injection == common_env_pkg::NEVER_ERROR;
				chip_length_error_injection == NEVER_ERROR;
			};
		new_tr.data = data;
		new_seq = dsi3_slave_seq::create_seq(new_tr);
		return new_seq;		
	endfunction
	
	virtual function dsi3_slave_tr create_transaction(dsi3_slave_sequencer_t sequencer);
		`uvm_create_on (req, sequencer)
		return req;
	endfunction
	
endclass

