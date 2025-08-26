class spi_cmd_buffer_status_seq extends base_dsi_master_seq;
	
	rand bit	crc_error;
	rand int	number_of_commands;
	
	constraint co_commands {number_of_commands inside {[1:100]};}
	constraint co_crc_error {crc_error dist {0:=1, 1:=4};}
	
	spi_cmd_buffer_status	buffer_status;

	`uvm_object_utils(spi_cmd_buffer_status_seq) 
    
	function new(string name = "");
		super.new("spi_cmd_buffer_status_seq");
	endfunction : new

	virtual task run_tests();
		int command_size;
		spi_read_master_register_seq	read_sequence;
		buffer_status = new(regmodel.SPI_CMD_STAT.ring_buffer_registers, "spi_cmd_buffer_status");
		
		buffer_status.get_current_status();
		#1us;
		
		command_size = 0;
		
		log_sim_description($sformatf("send %1d commands with crc_error=%1b", number_of_commands, crc_error), 2);
		`spi_frame_begin
			`spi_frame_create(spi_dsi_wait_seq, wait_time==500; channel_bits == 2'b11;)
			repeat(number_of_commands) begin
				randcase
					1: `spi_frame_create(spi_crm_seq, )
					1: `spi_frame_create(spi_dsi_wait_seq, )
					1: `spi_frame_create(spi_pdcm_seq, )
					1: `spi_frame_create(spi_clear_dsi_data_buffers_seq, )
//					1: `spi_frame_create(spi_clear_dsi_command_queue_seq, )
					1: `spi_frame_create(spi_sync_dsi_channels_seq, )
				endcase
			end
			
			foreach (frame.commands[i]) begin
				command_size += frame.commands[i].get_word_count();
				buffer_status.write(frame.commands[i].get_word_count());
			end
			
			begin
				`uvm_create(read_sequence)
				buffer_status.randomize_with_addresses(read_sequence);
				frame.add_command(read_sequence);
			end
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == (~crc_error);)
		`spi_frame_end
		
		log_sim_description($sformatf("command_size = %1d", command_size), 3);
		
		// check intermediate values before buffer is cleared
		buffer_status.check_read_sequence(read_sequence);
		
		#1000us;
		
		if (crc_error)	buffer_status.invalidate();
		else begin
			buffer_status.validate();
			buffer_status.read(command_size);
		end
		buffer_status.compare_buffer_registers();
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == '1;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;
		
	endtask
	
endclass