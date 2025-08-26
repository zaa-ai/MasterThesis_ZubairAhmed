/**
 * Class: spi_master_register_seq
 * 
 * Send CRM command sequences.
 */
class spi_crm_seq extends spi_dsi_command_seq;
	
	rand bit broad_cast;
	rand bit dsi3_crc_correct;
	rand dsi3_crm_packet crm_packet;
	
	rand logic[15:0] defined_data[$];
	
	`uvm_object_utils_begin(spi_crm_seq)
		`uvm_field_int (broad_cast, UVM_DEFAULT)
		`uvm_field_int (dsi3_crc_correct, UVM_DEFAULT)
		`uvm_field_object (crm_packet, UVM_DEFAULT)
	`uvm_object_utils_end
	
	constraint co_defined_data {soft defined_data.size() == 0;}

	covergroup cov_crm;
		option.per_instance = 0;
		coverpoint channel_bits;
		coverpoint broad_cast;	
		coverpoint dsi3_crc_correct;
		cross broad_cast, dsi3_crc_correct, channel_bits;
	endgroup
		
	/************************ Methods declarations ************************/
	function new(string name = "CRM Transmit");
		super.new(name);
		crm_packet = new();
		cov_crm = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_crm.sample();
	endfunction
	
	function void post_randomize();
		if(crm_packet.randomize() with {crc_correct == dsi3_crc_correct;} != 1) `uvm_error(this.get_name(), "randomization failed");
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_CRM;
	endfunction
		
	virtual function int get_word_count();
		return 3;
	endfunction	
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			logic[15:0] word = super.get_word(0);
			word[0] = broad_cast;
			return word;
		end
		if(index == 1) return (defined_data.size() > 0) ? defined_data[0] : crm_packet.get_word(0);
		if(index == 2) return (defined_data.size() > 1) ? defined_data[1] : crm_packet.get_word(1);
		return super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(data_in.size() < get_word_count()) begin
			return 0;
		end 
		broad_cast = data_in[0][0];
		crm_packet.set_data('{data_in[1], data_in[2]});
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("CRM: channels %04b, BC=%1b, 0x%04h 0x%04h", channel_bits, broad_cast, crm_packet.get_word(0), crm_packet.get_word(1));
	endfunction
endclass


