/**
 * Class: spi_read_pdcm_frame_seq
 * 
 * Read CRM data buffer.
 */
class spi_read_pdcm_frame_seq extends spi_read_dsi_data_seq;
	
	spi_pdcm_frame_header frame_header[$];
	
	`uvm_object_utils(spi_read_pdcm_frame_seq)
	
	/************************ Methods declarations ************************/
	
	function new(string name = "Read PDCM Frame");
		super.new(name);
		cov_read_pdcm = new();
	endfunction
	
	covergroup cov_read_pdcm;
		option.per_instance = 0;
		coverpoint channel_bits;
	endgroup
	
	virtual function spi_cmd_type get_command_code();
		return CMD_READ_PDCM_PACKETS;
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_read_pdcm.sample();
		foreach(frame_header[i]) begin
			frame_header[i].sample_cov();
		end
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
				tdma_scheme_pdcm scheme;
				scheme = tdma_scheme_upload_listener::schemes[i];
				count += 1; // frame header
				if(scheme.valid == 1'b1) begin
					foreach(scheme.packets[i]) begin
						if(scheme.packets[i].enable) begin
							count += 1; // packet header
							count += int'($ceil(scheme.packets[i].symbol_count / 4.0));	
						end
						else begin
							break;
						end
					end
				end
			end
		end
		return count;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) begin
			return super.get_word(0);
		end
		return {CMD_READ_PDCM_PACKETS, get_filler(index-1)};
	endfunction
	
	virtual function string convert2string();
		string s = "";
		s = $sformatf("read PDCM frame: channels 0b%02b", channel_bits);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			tdma_scheme_pdcm scheme = tdma_scheme_upload_listener::schemes[channel];
			if(scheme.valid == 1'b1) begin
				spi_pdcm_frame_header frame_header = get_frame_header(channel, 1'b0);
				if(frame_header != null) begin
					s = {s, $sformatf("\n channel 0b%02b [%s] %0d packets", channel, (frame_header.get_value(PC) == 1'b1) ? "PC" : "  " , frame_header.packet_count )};
					foreach(scheme.packets[packet_index]) begin
						if(scheme.packets[packet_index].enable == 1'b1) begin
							spi_dsi_data_packet data_packet = get_data_packet(channel, packet_index, 1'b0);
							if(data_packet != null) begin
								s = {s, $sformatf("\n %2d %s| %3d symbols: ", packet_index, packet_flags_to_string(data_packet), data_packet.symbol_count)};
								foreach(data_packet.data[word_index]) begin
									s = {s, $sformatf(" 0x%4h", data_packet.data[word_index])};						
								end
							end
						end
					end
				end
			end
			else begin
				s = {s, $sformatf("\n channel 0b%02b - no TDMA scheme", channel)};
			end
		end
		return s;
	endfunction
	
	virtual function string packet_flags_to_string(spi_dsi_data_packet data_packet);
		string s = "";
		dsi_response_flags iterator = iterator.first();
		do begin
			s = (data_packet.flags[iterator] == 1'b1) ? {s, $sformatf("|%3s", iterator.name())} : {s, "|   "};
			iterator = iterator.next();
		end while (iterator != iterator.first());
		return s;
	endfunction
	
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		bit result;
		int index = 2;
		result = super.create_from(data_in, data_out);
		if(!result) return result;
		
		data_packets.delete();
		frame_header.delete();
		
		
		for (int i=0; i < $bits(channel_bits); i++) begin
			if(channel_bits[i] == 1'b1) begin
				tdma_scheme_pdcm scheme;
				spi_pdcm_frame_header header;
				if(index < data_out.size() - 1) begin
					scheme = tdma_scheme_upload_listener::schemes[i];
					header = new();			
					header.channel_index = 2'(i);
					header.packet_count = data_out[index][7:0];
					header.set_values(data_out[index]);
					frame_header.push_back(header);
					index++;
					
					if(scheme.valid == 1'b1) begin
						foreach(scheme.packets[j]) begin
							if(index >= data_out.size() - 1) begin
								// skip if not enough words were received
								break;
							end
							if(scheme.packets[j].enable) begin
								int word_count = (int'($ceil(scheme.packets[j].symbol_count/4.0)) + 1);
								data_packets.push_back(create_data_packet(data_out, i, word_count, index));
							end
							else begin
								break;
							end
						end
					end
				end
			end
		end
		create_fillers(data_in);
		return 1'b1; 
	endfunction
	
	virtual function spi_pdcm_frame_header get_frame_header(logic[1:0] channel_index, bit error_if_header_is_missing = 1'b1);
		foreach(frame_header[i]) begin
			if(frame_header[i].channel_index == channel_index) begin
				return frame_header[i];
			end
		end
		if(error_if_header_is_missing == 1'b1) begin
			`uvm_error(this.get_type_name(), $sformatf("No frame header exists for channel of index %0d!", channel_index))
		end
		return null;
	endfunction
	
	// check packet count in frame header	
	virtual function void expect_packet_count(logic[1:0] channel_index, logic[7:0] expected_packet_count);
		spi_pdcm_frame_header frame_header = get_frame_header(channel_index);
		if(frame_header != null && frame_header.packet_count != expected_packet_count) begin
			`uvm_error(this.get_type_name(), $sformatf("Unexpected packet count in frame header at channel %0d, expected %0d, got %0d!", channel_index, expected_packet_count, frame_header.packet_count))
		end
	endfunction

	// check flags of frame header
	virtual function void expect_frame_header_flags(logic[1:0] channel_index, pdcm_frame_header_flags expected_flags[$]);
		spi_pdcm_frame_header frame_header = get_frame_header(channel_index);
		if(frame_header != null) begin
			flags_container #(pdcm_frame_header_flags) flags = new();
			flags.set_flags(expected_flags);
			void'(frame_header.check_flags_are_equal(flags, $sformatf("Unexpected flags in frame header at channel %0d!", channel_index)));
		end
	endfunction
	
	virtual function void get_data_packets(logic[1:0] channel_index, ref spi_dsi_data_packet packets[$]);
		foreach(data_packets[i]) begin
			if(data_packets[i].channel_index == channel_index) begin
				packets.push_back(data_packets[i]);
			end
		end
	endfunction
	
	virtual function spi_dsi_data_packet get_data_packet(logic[1:0] channel_index, int packet_index, bit error_if_packet_is_missing = 1'b1);
		spi_dsi_data_packet read_packets[$];
		get_data_packets(channel_index, read_packets);
		if(packet_index < read_packets.size()) begin
			return read_packets[packet_index];
		end
		if(error_if_packet_is_missing == 1'b1) begin
			`uvm_error(this.get_type_name(), $sformatf("No data packet of index %0d exists for channel %0d!", packet_index, channel_index))
		end
	endfunction
	
	virtual function void expect_symbol_count(logic[1:0] channel_index, int packet_index, logic[7:0] expected_symbol_count);
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		if(packet != null && packet.symbol_count != expected_symbol_count) begin
			`uvm_error(this.get_type_name(), $sformatf("Unexpected symbol count at packet index %0d at channel %0d, expected %0d symbols, got %0d!", packet_index, channel_index, expected_symbol_count, packet.symbol_count))
		end
	endfunction
	
	virtual function logic[7:0] get_symbol_count(logic[1:0] channel_index, int packet_index);
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		return packet.symbol_count;
	endfunction
	
	virtual function void expect_packet_data(logic[1:0] channel_index, int packet_index, int word_index, logic[15:0] expected_data);
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		if(packet != null) begin
			if(word_index >= packet.data.size()) begin
				`uvm_error(this.get_type_name(), $sformatf("No data for index %0d exists in in packet %0d. Only %0d data words contained at channel %0d", word_index, packet_index, packet.data.size(), channel_index))
			end 
			else if(packet.data[word_index] != expected_data) begin
				`uvm_error(this.get_type_name(), $sformatf("Unexpected data at packet index %0d at channel %0d at word index %0d, expected 0x%04h, got 0x%04h!", packet_index, channel_index, word_index, expected_data, packet.data[word_index]))
			end
		end
	endfunction
	
	virtual function void expect_packet(logic[1:0] channel_index, int packet_index, dsi3_packet expected_packet, bit ignore_crc = 1'b0);
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		if(packet != null) begin
			logic[15:0] expected_words[$];
			if (convert_queue#(4, 16)::convert(expected_packet.data, expected_words, 1)) `uvm_error(this.get_type_name(), "failed to convert queue of expected data")
			foreach(expected_words[i]) begin
				if(packet.data[i] != expected_words[i]) begin
					`uvm_error(this.get_type_name(), $sformatf("Unexpected data in channel %0d at packet index %0d at word index %0d, expected 0x%04h, got 0x%04h!", channel_index, packet_index, i, expected_words[i], packet.data[i]))
				end	
			end
			expect_symbol_count(channel_index, packet_index, expected_packet.data.size());
			if(ignore_crc == 1'b0 && packet.get_value(CRC) != ~expected_packet.crc_correct) begin
				`uvm_error(this.get_type_name(), $sformatf("Unexpected CRC flag in channel %0d at packet index %0d, expected %b, got %b!", channel_index, packet_index, ~expected_packet.crc_correct, packet.get_value(CRC)))
			end
		end
	endfunction
	
	virtual function void expect_flag(logic[1:0] channel_index, int packet_index, dsi_response_flags flag);
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		if(packet != null) begin
			packet.check_value(flag, 1'b1, $sformatf("Unexpected flag %s at packet index %0d in channel %0d!", flag.name, packet_index, channel_index));
		end
	endfunction
	
	virtual function bit has_flag(logic[1:0] channel_index, int packet_index, dsi_response_flags flag);
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		if(packet != null) begin
			return packet.get_value(flag);
		end
		return 1'b0;
	endfunction
	
	virtual function void expect_flags(logic[1:0] channel_index, int packet_index, dsi_response_flags expected_flags[$], dsi_response_flags ignore_flags[$] = {});
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		if(packet != null) begin
			flags_container #(dsi_response_flags) flags = new();
			flags.set_flags(expected_flags);
			void'(packet.check_flags_are_equal(flags, $sformatf("Unexpected flags at packet %0d at channel %0d!", packet_index, channel_index), ignore_flags));
		end
	endfunction
	
	/**
	 * Expect empty data (including symbol count and flags) at given channel.
	 */
	virtual function void expect_empty(logic[1:0] channel_index, int packet_index);
		expect_empty_data(channel_index, packet_index, {});
	endfunction
	
	/**
	 * Expect empty data (including symbol count) at given channel.
	 */
	virtual function void expect_empty_data(logic[1:0] channel_index, int packet_index, dsi_response_flags expected_flags[$]);
		spi_dsi_data_packet packet = get_data_packet(channel_index, packet_index);
		
		expect_flags(channel_index, packet_index, expected_flags);
		
		expect_symbol_count(channel_index, packet_index, 8'd0);
		if(packet != null) begin
			foreach(packet.data[i]) begin
				if(packet.data[i] != 16'h0000) begin
					`uvm_error(this.get_type_name(), $sformatf("Unexpected data in packet %0d at channel %0d at word index %0d, expected 0x0000, got 0x%04h!", packet_index, channel_index, i, packet.data[i]))
				end	
			end
		end		
	endfunction
	
endclass


