class pdcm_voltage_error_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_voltage_error_seq)

	function new(string name = "");
		super.new("pdcm_voltage_error");
	endfunction
	
	task run_tests();
		tdma_scheme_pdcm_denso_15 scheme = new();
		log_sim_description("receive packets with voltage error (VE) on all channels", LOG_LEVEL_SEQUENCE);
		
		get_checker_config().expect_PDCM_voltage_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_voltage_error_in_dsi_packet[1] = {};
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			foreach (scheme.packets[packet_index]) begin
				log_sim_description($sformatf("voltage error in channel %0d at packet index %0d", channel, packet_index), LOG_LEVEL_OTHERS);
				
				get_checker_config().expect_PDCM_voltage_error_in_dsi_packet[channel] = {packet_index};
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				fork
					begin
						#(scheme.pdcm_period * 1us);
					end
					begin
						time delay_after_pulse = scheme.packets[packet_index].get_earliest_start_time();
						time duration = scheme.packets[packet_index].symbol_count * 3 * scheme.chiptime * 1.05 * 1us;
						@(negedge m_dsi3_master_agent[channel].m_config.vif.cable.Voltage);
						#delay_after_pulse;
						set_dsi_uv_for_channel(channel, 1'b1);
						#duration;
						registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.DSIUV, 1'b1);
						set_dsi_uv_for_channel(channel, 1'b0);
					end
				join

				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#100us;
			end
		end
		get_checker_config().expect_PDCM_voltage_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_voltage_error_in_dsi_packet[1] = {};
		#500us;
	endtask
endclass
