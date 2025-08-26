
class upload_tdma_scheme_seq extends base_dsi_master_seq;
	
	tdma_scheme_pdcm scheme;
	rand logic[project_pkg::DSI_CHANNELS-1:0] channels;
	
	`uvm_object_utils_begin (upload_tdma_scheme_seq)
		`uvm_field_int (channels, UVM_DEFAULT | UVM_BIN )
		`uvm_field_object (scheme, UVM_DEFAULT )
	`uvm_object_utils_end
	
	function new(string name = "");
		super.new("upload_tdma_scheme");
	endfunction : new
	
	task run_tests();
		int packet_count = scheme.get_packet_count();
		
		`spi_frame_begin
			for (int i = 0; i < packet_count; i++) begin
				tdma_scheme_packet next_packet = scheme.packets[i];	
			
				`spi_frame_create(spi_upload_tdma_packet_seq,
					channel_bits == channels;
					packet_index == 4'(i);
					tdma_packet.earliest_start_time == next_packet.earliest_start_time;
					tdma_packet.latest_start_time 	== next_packet.latest_start_time;
					tdma_packet.id_symbol_count		== next_packet.id_symbol_count;
					tdma_packet.symbol_count 		== next_packet.symbol_count;)
			end
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == channels; packet_count == 4'(local::packet_count); pdcm_period == 16'(scheme.pdcm_period);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
		
		`uvm_info(get_type_name(), $sformatf("uploaded TDMA scheme:\n %s", scheme.convert2string()), UVM_MEDIUM)
	endtask
	
endclass