/**
 * Class: spi_upload_tdma_packet_seq
 * 
 * Upload a single TDMA packet.
 */
class spi_upload_tdma_packet_seq extends spi_dsi_command_seq;
	
	rand logic[3:0] packet_index;
	rand tdma_scheme_packet_pdcm tdma_packet;
	
	`uvm_object_utils_begin(spi_upload_tdma_packet_seq)
		`uvm_field_int(packet_index, UVM_DEFAULT | UVM_DEC)
		`uvm_field_object (tdma_packet, UVM_DEFAULT)
	`uvm_object_utils_end
	
	function new(string name = "Upload TDMA Packet");
		super.new(name);
		tdma_packet = new();
		cov_upload_tdma = new();
	endfunction
	
	covergroup cov_upload_tdma;
		option.per_instance = 0;
		coverpoint channel_bits;
		coverpoint packet_index;	
		cross packet_index, channel_bits;
	endgroup
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_upload_tdma.sample();
		tdma_packet.sample_cov();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_UPLOAD_TDMA;
	endfunction
		
	virtual function int get_word_count();
		return 4;
	endfunction	
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			logic[15:0] cmd = super.get_word(0);
			cmd[5] = 1'b1;
			cmd[3:0] = packet_index;
			return cmd;
		end
		if(index == 1) return tdma_packet.earliest_start_time;
		if(index == 2) return tdma_packet.latest_start_time;
		if(index == 3) return {tdma_packet.id_symbol_count, 6'h0, 8'(tdma_packet.symbol_count)};
		return super.get_word(index);
	endfunction
	
	virtual function bit starts_with(logic[15:0] word);
		return super.starts_with(word) && word[5] == 1'b1;
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(data_in.size() < get_word_count()) begin
			return 0;
		end
		if(data_in[0][5] != 1'b1) return 1'b0;
		packet_index = data_in[0][3:0];
		tdma_packet.earliest_start_time = data_in[1];
		tdma_packet.latest_start_time = data_in[2];
		tdma_packet.id_symbol_count = dsi3_pkg:: sid_length_e'(data_in[3][15:14]);
		tdma_packet.symbol_count = data_in[3][7:0];
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("Upload TDMA packet of index %0d for channels %02b", packet_index, channel_bits);
	endfunction
	
endclass


