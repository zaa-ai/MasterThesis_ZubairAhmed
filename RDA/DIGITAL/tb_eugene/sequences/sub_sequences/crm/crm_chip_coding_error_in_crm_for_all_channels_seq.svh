class crm_chip_coding_error_in_crm_for_all_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_chip_coding_error_in_crm_for_all_channels_seq)
	
	function new(string name = "");
		super.new("crm_chip_coding_error_in_crm_for_all_channels");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("receive packets with chip coding error (SE) on all channels", LOG_LEVEL_SEQUENCE);
		
		`ifdef GATE_LEVEL
			`uvm_info(get_type_name(), "skipped sequence, this sequence cannot be executed at gate level", UVM_MEDIUM)
			return;
		`endif
		
		repeat(10) begin
			for (int error_channel=0; error_channel < project_pkg::DSI_CHANNELS; error_channel++) begin
				spi_read_crm_data_packets_seq read;
				dsi3_crm_packet packets[$];
				int delay = $urandom_range(325, 342);
				
				log_sim_description($sformatf("receive symbol coding error at channel %0d with delay of %1dus", error_channel, delay), LOG_LEVEL_OTHERS);
				
				checker_config::get().enable_all_master_transmission_checkers();
				checker_config::get().set_master_transmission_checker_enable(error_channel, 1'b0);
				
				create_valid_CRM_packets_with_data(packets, 2'b11);

				check_dab(1'b1);
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				wait_for_voltage_edge_at_channel(error_channel);
				#(delay * 1us);
				uvm_hdl_force_time($sformatf(`STRING_OF(`DSI_CHIP_IN_PATH), error_channel), dsi3_pkg::CX, 4us); //FIXME: one cannot proof forcing was successful
								
				wait_for_dab(500us, 1'b1);
				#30us;
				
				`spi_frame_begin
					`spi_frame_send(read, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end

				// check results
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					dsi_response_flags expected_flags[$] = {};
					if(!packets[channel].crc_correct) expected_flags.push_back(CRC);
					if(channel == error_channel) begin
						logic[7:0] symbol_count = read.get_symbol_count(2'(channel));
						if(symbol_count != 8'd8) begin
							read.expect_flag( 2'(channel), SCE);
						end
						read.expect_flag( 2'(channel), SE); // expect SE flag
					end
					else begin
						read.expect_symbol_count(2'(channel), 8'd8);
						read.expect_flags( 2'(channel), expected_flags);
						read.expect_packet(2'(channel), packets[channel]);
					end
				end
			end
		end
		checker_config::get().enable_all_master_transmission_checkers();
		#100us;
	endtask
endclass
