/**
 * Class: spi_read_crm_data_packets_seq
 * 
 * Read CRM data buffer.
 */
class spi_read_crm_data_packets_seq extends spi_read_dsi_data_seq;
	
	`uvm_object_utils(spi_read_crm_data_packets_seq)

	/************************ Methods declarations ************************/
	
	function new(string name = "Read CRM Data Packets");
		super.new(name);
		cov_read_crm = new();
	endfunction
	
	covergroup cov_read_crm;
		option.per_instance = 0;
		coverpoint channel_bits;
	endgroup
	
	virtual function spi_cmd_type get_command_code();
		return CMD_READ_CRM_PACKETS;
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_read_crm.sample();
	endfunction
		
	virtual function int get_word_count();
		if(incomplete == 1'b1) begin
			return incomplete_word_count;
		end
		else begin
			return calculate_word_count(channel_bits);
		end
	endfunction	

	static function int calculate_word_count(logic [project_pkg::DSI_CHANNELS-1:0] _channel_bits);
		int count = 1;
		for (int i=0; i < $bits(_channel_bits); i++) begin
			if(_channel_bits[i] == 1'b1) begin
				count += 3;	
			end
		end
		return count;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			return super.get_word(0);
		end
		return {CMD_READ_CRM_PACKETS, get_filler(index-1)};
	endfunction
	
	virtual function string convert2string();
		return $sformatf("READ CRM DATA PACKETS: channels %02b", channel_bits);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		bit result;
		result = super.create_from(data_in, data_out);
		if(!result) return result;
		create_data_packets(data_out);
		create_fillers(data_in);
		return 1'b1; 
	endfunction
	
	function void create_data_packets(input logic[15:0] data_out[$]);
		int index = 2;
		data_packets.delete();
		for (int i=0; i < $bits(channel_bits); i++) begin
			if(channel_bits[i] == 1'b1 && index < data_out.size() - 1) begin
				data_packets.push_back(create_data_packet(data_out, i, 3, index));
			end
		end
	endfunction
	
	virtual function string crm_packet_to_string(spi_dsi_data_packet packet);
		string s = "";
		dsi_response_flags iterator = iterator.first();
		do begin
			s = (packet.flags[iterator] == 1'b1) ? {s, $sformatf("|%s", iterator.name())} : {s, "|-"};
			iterator = iterator.next();
		end while (iterator != iterator.first());
		
		s = {s, $sformatf("| (SC=%0d) 0x%4h 0x%4h", packet.symbol_count, packet.data[0], packet.data[1])};
		return s;
	endfunction
	
	virtual function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
		create_data_packets(data_out);
		foreach(data_packets[i]) begin
			spi_dsi_data_packet packet = data_packets[i];
			`uvm_record_field($sformatf("channel_%0d", i), crm_packet_to_string(packet))
		end
	endfunction
	
	/**
	 * Gets data packet for a given channel and packet index.
	 * Returns null if no such packet exists.
	 */
	virtual function spi_dsi_data_packet get_data_packet(logic[1:0] channel_index,  bit error_if_packet_is_missing = 1'b1);
		foreach(data_packets[i]) begin
			if(data_packets[i].channel_index == channel_index) begin
				return data_packets[i];
			end
		end
		if(error_if_packet_is_missing) begin
			`uvm_error(this.get_type_name(), $sformatf("No data packet exists for channel of index %0d!", channel_index))
		end
		return null;
	endfunction
	
	virtual function void expect_flags(logic[1:0] channel_index, dsi_response_flags expected_flags[$], dsi_response_flags ignore_flags[$] = {});
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		if(packet != null) begin
			flags_container #(dsi_response_flags) flags = new();
			flags.set_flags(expected_flags);
			void'(packet.check_flags_are_equal(flags, $sformatf("Unexpected flags at channel %0d!", channel_index), ignore_flags));
		end
	endfunction
	
	/**
	 * Checks that a single flag is set in packet status.
	 */
	virtual function void expect_flag(logic[1:0] channel_index, dsi_response_flags flag);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		if(packet != null) begin
			packet.check_value(flag, 1'b1, $sformatf("Unexpected flag %s at channel %0d!", flag.name(), channel_index));
		end
	endfunction
	
	virtual function bit has_flag(logic[1:0] channel_index, dsi_response_flags flag);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		if(packet != null) begin
			return packet.get_value(flag);
		end
		return 1'b0;
	endfunction
	
	virtual function void expect_symbol_count(logic[1:0] channel_index, logic[7:0] expected_symbol_count);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		if(packet != null && packet.symbol_count != expected_symbol_count) begin
			`uvm_error(this.get_type_name(), $sformatf("Unexpected symbol count at channel %0d, expected %0d symbols, got %0d!", channel_index, expected_symbol_count, packet.symbol_count))
		end
	endfunction

	virtual function logic[7:0] get_symbol_count(logic[1:0] channel_index);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		return packet.symbol_count;
	endfunction
	
	virtual function void expect_packet_data(logic[1:0] channel_index, int word_index, logic[15:0] expected_data);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		if(packet != null) begin
			if(word_index >= packet.data.size()) begin
				`uvm_error(this.get_type_name(), $sformatf("No data for index %0d exists. Only %0d data words contained at channel %0d", word_index, packet.data.size(), channel_index))
			end 
			else if(packet.data[word_index] != expected_data) begin
				`uvm_error(this.get_type_name(), $sformatf("Unexpected data at channel %0d at word index %0d, expected 0x%04h, got 0x%04h!", channel_index, word_index, expected_data, packet.data[word_index]))
			end
		end
	endfunction
	
	virtual function void expect_packet_size(logic[1:0] channel_index, int expected_packet_size);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		if(packet != null) begin
			if(expected_packet_size != packet.data.size()) begin
				`uvm_error(this.get_type_name(), $sformatf("Unexpected packet size. Only %0d data words contained in channel %0d, expected %0d", packet.data.size(), channel_index, expected_packet_size))
			end 
		end
	endfunction
	
	/**
	 * Check against a given dsi3_packet.
	 * Checks:
	 *  - all read words match to content of dsi3_packet
	 *  - symbol count
	 *  - CRC flag is set if dsi3_packet has wrong CRC
	 */
	virtual function void expect_packet(logic[1:0] channel_index, dsi3_packet expected_packet, bit ignore_crc = 1'b0);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		if(packet != null) begin
			logic[15:0] expected_words[$];
			if (convert_queue#(4, 16)::convert(expected_packet.data, expected_words, 1)) `uvm_error(this.get_type_name(), "failed to convert queue of expected data")
			foreach(expected_words[i]) begin
				if(packet.data[i] != expected_words[i]) begin
					`uvm_error(this.get_type_name(), $sformatf("Unexpected data at channel %0d at word index %0d, expected 0x%04h, got 0x%04h!", channel_index, i, expected_words[i], packet.data[i]))
				end	
			end
			expect_symbol_count(channel_index, expected_packet.data.size());
			if(ignore_crc == 1'b0 && packet.get_value(CRC) != ~expected_packet.crc_correct) begin
				`uvm_error(this.get_type_name(), $sformatf("Unexpected CRC flag at channel %0d, expected %b, got %b!", channel_index, ~expected_packet.crc_correct, packet.get_value(CRC)))
			end
		end
	endfunction
	
	virtual function void expect_spi_data_packet(logic[1:0] channel_index, spi_dsi_data_packet expected_packet);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		void'(packet.check_flags_are_equal(expected_packet, "", '{}));
		expect_symbol_count(channel_index, expected_packet.symbol_count);
		foreach (packet.data[i]) begin
			expect_packet_data(channel_index, i, expected_packet.data[i]);
		end
	endfunction
	
	/**
	 * Expect empty data (including symbol count and flags) at given channel.
	 */
	virtual function void expect_empty(logic[1:0] channel_index);
		expect_empty_data(channel_index, {});
	endfunction
	
	/**
	 * Expect empty data (including symbol count) at given channel.
	 */
	virtual function void expect_empty_data(logic[1:0] channel_index, dsi_response_flags expected_flags[$]);
		spi_dsi_data_packet packet = get_data_packet(channel_index);
		expect_flags(channel_index, expected_flags);
		expect_symbol_count(channel_index, 8'd0);
		if(packet != null) begin
			foreach(packet.data[i]) begin
				if(packet.data[i] != 16'h0000) begin
					`uvm_error(this.get_type_name(), $sformatf("Unexpected data at channel %0d at word index %0d, expected 0x0000, got 0x%04h!", channel_index, i, packet.data[i]))
				end	
			end
		end		
	endfunction
	
endclass


