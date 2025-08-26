class dsi_cmd_buffer_status_seq extends base_dsi_master_seq;
	
	rand bit	crc_error;
	rand int	number_of_commands;
	
	constraint co_commands {number_of_commands inside {[1:100]};}
	constraint co_crc_error {crc_error dist {0:=1, 1:=4};}
	
	dsi_cmd_buffer_status	buffer_status[project_pkg::DSI_CHANNELS-1:0];

	`uvm_object_utils(dsi_cmd_buffer_status_seq) 
    
	function new(string name = "");
		super.new("dsi_cmd_buffer_status_seq");
	endfunction : new

	virtual task run_tests();
		int command_size[project_pkg::DSI_CHANNELS-1:0];
		spi_read_master_register_seq	read_sequences[project_pkg::DSI_CHANNELS-1:0];
		spi_command_frame_seq frame; 
		
		for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			int base_address = int'(project_pkg::BASE_ADDR_DSI_CMD_BUF[channel]);
			buffer_status[channel] = new(base_address, regmodel.DSI_CMD_STAT[channel].ring_buffer_registers, "dsi_cmd_buffer_status");
		end
		
		foreach(buffer_status[channel])
			buffer_status[channel].get_current_status();
		
		#1us;
		
		foreach(command_size[channel])
			command_size[channel] = 0;
		
		log_sim_description($sformatf("send %1d commands with crc_error=%1b", number_of_commands, crc_error), 2);
		begin 
			`uvm_create_on(frame, m_spi_agent.m_sequencer) 
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time==500;)
			repeat(number_of_commands) begin
				randcase
					1: `spi_frame_create(spi_crm_seq, )
					1: `spi_frame_create(spi_dsi_wait_seq, )
					1: `spi_frame_create(spi_pdcm_seq, )
					1: `spi_frame_create(spi_sync_dsi_channels_seq, )
				endcase
			end
			
			foreach(read_sequences[channel]) begin
				`uvm_create(read_sequences[channel])
				buffer_status[channel].randomize_with_addresses(read_sequences[channel]);
				frame.add_command(read_sequences[channel]);
			end
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == (~crc_error);)
		`spi_frame_end
		
		
		#100us;
		
		if (crc_error) begin // no change!
			foreach(buffer_status[channel]) begin
				buffer_status[channel].compare_buffer_registers();
			end
		end
		else begin
			foreach (frame.commands[i]) begin
				spi_dsi_command_seq	dsi_command;
				if ($cast(dsi_command, frame.commands[i])) begin
					for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
						if (dsi_command.channel_bits[channel] == 1'b1) begin
							command_size[channel] += dsi_command.get_word_count();
							buffer_status[channel].write(dsi_command.get_word_count());
						end
					end
				end
			end
			foreach(buffer_status[channel]) begin
				log_sim_description($sformatf("command_size[%1d] = %1d", channel, command_size[channel]), 3);
				buffer_status[channel].validate();
				buffer_status[channel].read(2);
			end
			foreach(buffer_status[channel]) begin
				buffer_status[channel].compare_buffer_registers();
			end
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == '1;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;
		
	endtask
	
endclass