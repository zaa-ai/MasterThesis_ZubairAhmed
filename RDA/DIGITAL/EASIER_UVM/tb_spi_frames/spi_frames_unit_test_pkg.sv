/**
 * Package: spi_frames_unit_test_pkg
 * 
 * package for the SPI frames unit test
 */
package spi_frames_unit_test_pkg;

	import uvm_pkg::*;
	import digital_signal_pkg::*;
	import dsi3_master_pkg::*;
	import dsi3_slave_pkg::*;
	import spi_pkg::*;
	import common_pkg::*;
	import common_env_pkg::*;
	import project_pkg::*;
	import edf_epm_model_pkg::*;
	
	task send_spi_tr_with_crc(spi_protocol_listener listener, logic[15:0] data_in[$], logic[15:0] data_out[$]);
		send_spi_tr(listener, data_in, data_out);
		send_spi_tr(listener, {crc_calculation_pkg::spi_calculate_correct_crc(data_in)}, {crc_calculation_pkg::spi_calculate_correct_crc(data_out)});
		#10us;
	endtask
	
	function static void send_spi_tr(spi_protocol_listener listener, logic[15:0] data_in[$], logic[15:0] data_out[$]);
		spi_tr tr;
		foreach(data_in[i]) begin
			tr = new();
			tr.tr_type = SPI_DATA;
			tr.data_in = data_in[i];
			tr.data_out = data_out[i];
			listener.write(tr);
		end
	endfunction
	
	function void set_tdma_scheme(logic[1:0] channels, int pdcm_period, int packet_symbols[$], shortint unsigned earliest_start_times[$], shortint unsigned latest_start_times[$]);
		if(packet_symbols.size() != earliest_start_times.size()) 	$error("size of packet_symbols queue does not match size of earliest_start_times queue");
		if(packet_symbols.size() != latest_start_times.size()) 		$error("size of packet_symbols queue does not match size of latest_start_times queue");
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel] == 1'b1) begin
				tdma_scheme_upload_listener::schemes[channel].valid = 1'b1;
				tdma_scheme_upload_listener::schemes[channel].pdcm_period = pdcm_period;
				foreach(packet_symbols[i]) begin
					tdma_scheme_upload_listener::schemes[channel].packets[i].enable = 1'b1;
					tdma_scheme_upload_listener::schemes[channel].packets[i].id_symbol_count = dsi3_pkg::SID_8Bit; // use some default
					tdma_scheme_upload_listener::schemes[channel].packets[i].symbol_count = packet_symbols[i];
					tdma_scheme_upload_listener::schemes[channel].packets[i].earliest_start_time = earliest_start_times[i];
					tdma_scheme_upload_listener::schemes[channel].packets[i].latest_start_time = latest_start_times[i];
				end
			end
			else begin
				tdma_scheme_upload_listener::schemes[channel].valid = 1'b0;
			end
		end
	endfunction
	
	`include "spi_frame_subscriber.svh"
	`include "spi_read_crm_subscriber.svh"
	`include "spi_read_pdcm_subscriber.svh"
	`include "logging_spi_sequencer.svh"
	`include "dsi3_transaction_recorder.svh"
	`include "dsi3_master_transmission_checker.svh"
	
	`include "top_config.svh"
	`include "top_env.svh"
	`include "top_test.svh"

endpackage


