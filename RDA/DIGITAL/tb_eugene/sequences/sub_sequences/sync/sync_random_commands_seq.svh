class sync_random_commands_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(sync_random_commands_seq) 
	
	function new(string name = "");
		super.new("sync_random_commands");
	endfunction
	
	virtual task run_tests();
		log_sim_description("synchronize mixed/random commands", LOG_LEVEL_SEQUENCE);

		transaction_recorder.enable_recorder();
		// disable sync PDCM feature
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 0);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, 0);
					
		repeat(30) begin
			string commands;
			int command_count = $urandom_range(2,5);
			time spi_end;
            time wait_time;
			tdma_scheme_pdcm scheme = new();
			if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			apply_tdma_scheme(scheme);
			
			`spi_frame_begin
				// some random commands
				for(int i=0; i<command_count; i++) begin
					append_random_transmit_commands(frame, commands);
					if(i != command_count-1) begin
						commands = $sformatf("%s, ", commands);
					end
				end
				log_sim_description($sformatf("sync %0d random commands (%s) using different SPI frames at all channels", command_count, commands), LOG_LEVEL_OTHERS);
				// sync all channels
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
				// CRM or PDCM on all channels
				randcase
					1 : `spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
					1 : `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				endcase
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                wait_time = get_wait_time(frame, scheme);
			`spi_frame_end
			spi_end = $time;
			#(wait_time);
			
			check_channel_sync(2'b11, 2'b11, spi_end);
			transaction_recorder.clear_all();
		end
		transaction_recorder.disable_recorder();
    endtask
    
    virtual function time get_wait_time(spi_command_frame_seq frame, tdma_scheme_pdcm scheme);
        time wait_time[project_pkg::DSI_CHANNELS-1:0];
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            for (int command_index = 0; command_index < frame.commands.size(); command_index++) begin
                case (frame.commands[command_index].get_type_name())
                    spi_pdcm_seq::type_name: begin
                        spi_pdcm_seq    seq;
                        void'($cast(seq, frame.commands[command_index]));
                        repeat(seq.pulse_count)
                            wait_time[channel] += (scheme.pdcm_period*1us);
                    end
                    spi_crm_seq::type_name: begin
                        wait_time[channel] += 450us;
                    end
                    spi_dsi_wait_seq::type_name: begin
                        spi_dsi_wait_seq    seq;
                        void'($cast(seq, frame.commands[command_index]));
                        wait_time[channel] += (seq.wait_time * 1us);
                    end
                endcase
            end
        end
        begin
            time max[$] = wait_time.max();
            if (max.size() > 0)
                return max[0] + 0.5ms;
            else 
                return 7ms;
        end
    endfunction
endclass