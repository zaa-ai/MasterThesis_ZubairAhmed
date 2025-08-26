/**
 * Class: spi_read_dsi_data_seq
 * 
 * Base class for all DSI data reading SPI commands.
 */
class spi_read_dsi_data_seq extends spi_dsi_command_seq;
	
	logic[11:0] fillers[$];
	spi_dsi_data_packet data_packets[$];
	
	// indicates that this read command was incomplete (less words that needed)
	bit incomplete = 1'b0;
	// gets number of words in case of an incomplete read command
	int incomplete_word_count = 0;
	
	`uvm_object_utils(spi_read_dsi_data_seq)
	
	/************************ Methods declarations ************************/
	
	function new(string name = "Read DSI data");
		super.new(name);
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		foreach(data_packets[i]) begin
			data_packets[i].sample_cov();
		end
	endfunction
	
	virtual function spi_mirroring_type get_mirroring_type();
		return spi_pkg::COMMAND_WORD_ONLY;
	endfunction

	virtual function spi_dsi_data_packet create_data_packet(input logic[15:0] data_out[$], input int channel_index, input int word_count, ref int index);
		spi_dsi_data_packet packet = new();
		packet.channel_index = 2'(channel_index);
		for (int i=0; i < word_count; i++) begin
			logic[15:0] next_word = data_out[index];
			if(i==0) begin
				packet.symbol_count = next_word[7:0];
				packet.set_values(next_word);
			end	else begin
				packet.data.push_back(next_word);
			end
			index++;
			if( index >= data_out.size() - 1) begin
				// skip if not enough words were received
				break;
			end
			if(incomplete == 1'b1 && index > incomplete_word_count) begin
				break;
			end
		end
		return packet;
	endfunction
	
	virtual function logic[11:0] get_filler(int index);
		while(index+1 > fillers.size()) begin
			fillers.push_back($urandom_range('hFFF, 'h0));
		end
		return fillers[index];
	endfunction
	
	virtual function void create_fillers(logic[15:0] data_in[$]);
		fillers.delete();
		for (int i = 0; i < get_word_count() - 1; i++) begin
			fillers.push_back(data_in[i+1][11:0]);
		end
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		int expected_word_count;
		incomplete = 1'b0;
		incomplete_word_count = 0;
		
		channel_bits = data_in[0][CHANNELS_MSB:CHANNELS_LSB];
		filler = data_in[0];
		expected_word_count = get_word_count();
		
		this.data_in.delete();
		this.data_out.delete();
		
		foreach(data_in[i]) begin
			if(i < expected_word_count) begin
				if(data_in[i][15:12] != get_command_code()) begin
					incomplete = 1'b1;
					incomplete_word_count = i;
					return 1'b1;
				end
				else begin			
					this.data_in.push_back(data_in[i]);
					this.data_out.push_back(data_out[i]);
				end
			end
		end
		return data_in.size() > expected_word_count;
	endfunction
	
endclass


