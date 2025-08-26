/**
 * Class: spi_frame_factory
 * 
 * Factory for creating SPI frames
 */
class spi_frame_factory #(int channel = -1) extends uvm_object;
	
	`uvm_object_param_utils(spi_frame_factory #(channel))

	function new(string name="spi_frame_factory");
		super.new(name);
	endfunction
	
	static function spi_command_frame_seq create_random_frame(spi_sequencer sequencer, int number_of_commands=-1);
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		append_random_commands(new_frame, number_of_commands);
		return new_frame;
	endfunction
	
	static function void append_random_commands(spi_command_frame_seq frame, int number_of_commands=-1, bit include_tx_crc=1'b1, bit include_tdma_upload=1'b1);
		if (number_of_commands == -1) begin
			number_of_commands = $urandom_range(200,1);
		end
		for (int command_index=0; command_index< number_of_commands; command_index++) begin
			spi_seq seq;
			randcase
				1 : begin
					seq = spi_seq_factory#(spi_read_status_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_crm_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_clear_dsi_data_buffers_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_clear_dsi_command_queue_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_dsi_wait_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_pdcm_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_sync_dsi_channels_seq)::create_seq();
				end
				include_tx_crc : begin
					seq = spi_seq_factory#(spi_tx_crc_request_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_write_master_register_seq)::create_seq();
				end
				include_tdma_upload : begin
					seq = spi_seq_factory#(spi_upload_tdma_packet_seq)::create_seq();
				end
				include_tdma_upload : begin
					seq = spi_seq_factory#(spi_validate_tdma_scheme_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_discovery_mode_seq)::create_seq();
				end
			endcase
			frame.add_command(seq);
		end
	endfunction
	
	static function void append_crc_command(spi_command_frame_seq frame);
		spi_seq seq;
		seq = spi_seq_factory#(spi_tx_crc_request_seq)::create_seq();
		frame.add_command(seq);
	endfunction
	
	
	static function spi_command_frame_seq create_random_frame_with_queue_commands(spi_sequencer sequencer, int number_of_commands=-1);
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		if (number_of_commands == -1)
			number_of_commands = $urandom_range(200,1);
		for (int command_index=0; command_index< number_of_commands; command_index++) begin
			spi_seq seq;
			randcase
				1 : begin
					seq = spi_seq_factory#(spi_crm_seq)::create_seq();
				end
				1 : begin
					seq = spi_seq_factory#(spi_write_master_register_seq)::create_seq();
				end
			endcase
			new_frame.add_command(seq);
		end
		
		return new_frame;
	endfunction
	
	static function spi_command_frame_seq create_frame_with_write_register_commands(spi_sequencer sequencer, int number_of_commands=-1);
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		if (number_of_commands == -1)
			number_of_commands = $urandom_range(200,1);
		for (int command_index=0; command_index< number_of_commands; command_index++) begin
			spi_seq seq;
			seq = spi_seq_factory#(spi_write_master_register_seq)::create_seq();
			new_frame.add_command(seq);
		end
		
		return new_frame;
	endfunction
	
	static function spi_command_frame_seq create_read_register_frame(spi_sequencer sequencer, int number_of_reads=1);
		spi_command_frame_seq new_frame = new();
		spi_read_master_register_seq seq;
		spi_seq seq_end;
		
		new_frame.set_sequencer(sequencer);
		if (number_of_reads == -1)
			number_of_reads = $urandom_range(200,1);
		seq = spi_seq_factory#(spi_read_master_register_seq)::create_seq();
		if(seq.randomize with {burst_addresses.size() == number_of_reads-1;} != 1) `uvm_error_context("spi_frame_factory", "randomization failed", seq);
		new_frame.add_command(seq);
		
		seq_end = spi_seq_factory#(spi_tx_crc_request_seq)::create_seq();
		new_frame.add_command(seq_end);
		
		return new_frame;
	endfunction
	
	static function spi_command_frame_seq create_frame_with_crm_commands_bc(spi_sequencer sequencer=null, int number_of_commands=-1, bit bc=1'b0);
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		if (number_of_commands == -1)
			number_of_commands = $urandom_range(200,1);
		for (int command_index=0; command_index< number_of_commands; command_index++) begin
			spi_crm_seq seq;
			seq = spi_seq_factory#(spi_crm_seq)::create_seq();
			seq.broad_cast = bc;
			if (channel >= 0) 
				seq.channel_bits = 1 << channel;
			new_frame.add_command(seq);
		end
		
		return new_frame;
	endfunction
	
	static function spi_command_frame_seq create_frame_with_crm_commands(spi_sequencer sequencer, int number_of_commands=-1);
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		if (number_of_commands == -1)
			number_of_commands = $urandom_range(200,1);
		for (int command_index=0; command_index< number_of_commands; command_index++) begin
			spi_seq seq;
			seq = spi_seq_factory#(spi_crm_seq)::create_seq();
			new_frame.add_command(seq);
		end
		
		return new_frame;
	endfunction
	
	static function spi_command_frame_seq create_frame_with_pdcm_commands(spi_sequencer sequencer, int number_of_commands=-1);
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		if (number_of_commands == -1)
			number_of_commands = $urandom_range(200,1);
		for (int command_index=0; command_index< number_of_commands; command_index++) begin
			spi_seq seq;
			seq = spi_seq_factory#(spi_pdcm_seq)::create_seq();
			new_frame.add_command(seq);
		end
		
		return new_frame;
	endfunction
	
	static function spi_command_frame_seq create_frame_with_a_pdcm_command(spi_sequencer sequencer, int periods=1);
		spi_pdcm_seq seq;
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		seq = spi_seq_factory#(spi_pdcm_seq)::create_seq();
		seq.pulse_count = periods;
		if (channel >= 0) 
			seq.channel_bits = 1 << channel;
		new_frame.add_command(seq);
		return new_frame;
	endfunction
	
	static function spi_command_frame_seq create_frame_with_tdma_scheme(tdma_scheme_pdcm scheme, bit add_crc_command);
		spi_command_frame_seq frame = new();
		spi_validate_tdma_scheme_seq 	validate_seq;
		spi_upload_tdma_packet_seq		packet_seq;
		
		foreach(scheme.packets[i]) begin
			packet_seq = new();
			void'(packet_seq.randomize() with {
				if (channel>=0) channel_bits == 2'(1<<channel);
				packet_index == 4'(i);
				tdma_packet.earliest_start_time == scheme.packets[i].earliest_start_time;
				tdma_packet.latest_start_time 	== scheme.packets[i].latest_start_time;
				tdma_packet.id_symbol_count		== scheme.packets[i].id_symbol_count;
				tdma_packet.symbol_count 		== scheme.packets[i].symbol_count;});
			frame.add_command(packet_seq);
		end
		validate_seq = spi_seq_factory#(spi_validate_tdma_scheme_seq)::create_seq();
		if (channel >= 0) 
			validate_seq.channel_bits = 1 << channel;
		validate_seq.packet_count = scheme.packets.size();
		validate_seq.pdcm_period = scheme.pdcm_period;
		frame.add_command(validate_seq);
		
		
		if (add_crc_command == 1'b1) begin
			spi_tx_crc_request_seq crc_seq =  new();
			void'(crc_seq.randomize with {mosi_crc_correct == 1'b1;});
			frame.add_command(crc_seq);
		end
		
		return frame;
	endfunction

endclass


