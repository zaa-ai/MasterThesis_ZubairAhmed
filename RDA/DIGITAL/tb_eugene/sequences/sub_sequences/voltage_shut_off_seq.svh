class voltage_shut_off_seq extends tvl_base_shut_off_seq;
	
	rand logic[project_pkg::DSI_CHANNELS-1:0] active_channels;
	rand time time_after_dsi_transmit;
	rand time time_before_dsi_transmit;
	rand logic use_pdcm;
	rand logic uv_n_ov;
	rand int wait_time_add;
	
	`uvm_object_utils_begin (voltage_shut_off_seq)
		`uvm_field_int (active_channels, UVM_DEFAULT | UVM_BIN )
		`uvm_field_int(time_after_dsi_transmit, UVM_DEFAULT | UVM_TIME )
	`uvm_object_utils_end
	
	constraint co_time {time_after_dsi_transmit < 360us;}
	constraint co_channels {active_channels > 2'd0;}
	
	function new(string name = "");
		super.new("voltage_shut_off");
	endfunction
	
	task run_tests();
		log_sim_description($sformatf("voltage shut off at %s with channels=%01b and time %8.2f", use_pdcm == 1'b0 ? "CRM" : "PDCM", active_channels, time_after_dsi_transmit/1.0us), LOG_LEVEL_SEQUENCE);
		
		if (use_pdcm == 1'b0) begin
			add_packets_crm(2'b11);
			add_packets_crm(active_channels);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
			`spi_frame_end
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1; crm_buffer == 1'b1;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'(4100 + wait_time_add);)
				`spi_frame_create(spi_crm_seq, channel_bits == active_channels; broad_cast == 1'b0;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == active_channels; wait_time == 50;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == ~active_channels; wait_time == 450;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end 
		else begin
			tdma_scheme_pdcm scheme = tdma_scheme_pdcm_factory::single_packet(8);
			scheme.packets[0].set_start_time_window(30, 50);
			scheme.pdcm_period = 300;
			
			add_packets_pdcm(2'b11);
			add_packets_pdcm(active_channels);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
				
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1; crm_buffer == 1'b1;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'(3800 + wait_time_add);)
				`spi_frame_create(spi_pdcm_seq, channel_bits == active_channels; pulse_count == 1;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == active_channels; wait_time == 50;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == ~active_channels; wait_time == 1050;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end
		
		fork
			begin
				#(time_before_dsi_transmit);
				if (active_channels[0] == 1'b1) @(negedge m_dsi3_master_agent[0].m_config.vif.cable.Voltage);
				if (active_channels[1] == 1'b1) @(negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
				//#(time_after_dsi_transmit);
				if (uv_n_ov == 1'b1) begin
					set_dsi_uv_for_channel(0, 1);
					set_dsi_uv_for_channel(1, 1);
				end else begin
					set_dsi_ov_for_channel(0, 1);
					set_dsi_ov_for_channel(1, 1);
				end
				#7.5ms;
				check_dsi_channels(2'b11, 1'b0);
			end
			//#8ms;
		join_any
		disable fork;
		
		check_registers_and_flags(1, 0);
		
		if (uv_n_ov == 1'b1) begin
			set_dsi_uv_for_channel(0, 0);
			set_dsi_uv_for_channel(1, 0);
		end else begin
			set_dsi_ov_for_channel(0, 0);
			set_dsi_ov_for_channel(1, 0);
		end
		
		#7.5ms;
		
		if (use_pdcm == 1'b0) begin
			spi_read_crm_data_packets_seq read_crm[1:0];
			`spi_frame_begin
				`spi_frame_send(read_crm[0], channel_bits == 2'b11;)
				`spi_frame_send(read_crm[1], channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		
			check_packets_crm(read_crm[0], 2'b11, {VE});
			check_packets_crm(read_crm[1], 2'b00, {VE});
		end 
		else begin
			spi_read_pdcm_frame_seq read_pdcm[1:0];
			`spi_frame_begin
				`spi_frame_send(read_pdcm[0], channel_bits == 2'b11;)
				`spi_frame_send(read_pdcm[1], channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			check_packets_pdcm(read_pdcm[0], 2'b11, {VE});
			check_packets_pdcm(read_pdcm[1], 2'b00, {VE});
		end
		#50us;
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
		
		#200us;
		check_dsi_channels(2'b11, 1'b1);
		
		if (use_pdcm == 1'b0) begin
			clear_slave_crm_scheme_fifos();
		end
	endtask
endclass
