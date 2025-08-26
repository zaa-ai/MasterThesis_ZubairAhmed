/**
 * Class: spi_protocol_listener
 *
 * UVM subscriber which listens to SPI transactions and transforms it to a SPI frame containing several sequences broadcasted by uvm_analysis_ports
 */
class spi_protocol_listener extends uvm_subscriber #(spi_tr);
	
	uvm_analysis_port #(spi_command_frame_seq) spi_command_frame_port;
	uvm_analysis_port #(spi_read_crm_data_packets_seq) spi_read_crm_port;
	uvm_analysis_port #(spi_read_pdcm_frame_seq) spi_read_pdcm_port;
	
	local bit frame_started;
	local time command_begin_time = 0;
	
	`uvm_component_utils (spi_protocol_listener)
	
	protected	logic[15:0] data_in[$] = '{};
	protected	logic[15:0] data_out[$] = '{};
	protected	spi_command_frame_seq next_frame;
	
	function new(string name = "spi_protocol_listener", uvm_component parent);
		super.new(name, parent);
		spi_command_frame_port = new("spi_command_frame_port", this);
		spi_read_crm_port = new("spi_read_crm_port", this);
		spi_read_pdcm_port = new("spi_read_pdcm_port", this);
		frame_started = 1'b0;
		next_frame = new();
	endfunction
	
	
	virtual function void write(spi_tr t);
		if(t.tr_type == spi_pkg::SPI_DATA) begin
			spi_seq next_command;
			if (frame_started == 1'b0) begin
				void'(begin_tr(next_frame));
				frame_started = 1'b1;
			end
			if(command_begin_time == 0) begin
				command_begin_time = t.get_begin_time();
			end
			
			data_in.push_back(t.data_in);
			data_out.push_back(t.data_out);
			
			next_command = create_command(data_in, data_out);
			if(next_command != null) begin
				bit is_crc_command, is_reset_command;
				logic[15:0] mask = create_compare_mask(t.bit_count);
				// take and re-calculate CRC from "SPI frame CRC command"
				is_crc_command = handle_tx_crc_command(next_frame, next_command, mask);
				is_reset_command = handle_reset_command(next_command);
				
				// set begin/end times	
				next_command.begin_tr(command_begin_time);
				next_command.end_tr(t.get_end_time());
				command_begin_time = 0;

				next_frame.add_command(next_command);
				next_command.sample_cov();
				
				// remove already converted words
				for (int i=0; i < next_command.get_word_count(); i++) begin
					next_frame.data_in.push_back(data_in.pop_front());
					next_frame.data_out.push_back(data_out.pop_front());
				end
				
				// check if previous command was a read (CRM or PDCM) -> send these commands to its analysis ports  
				if(next_frame.commands.size() > 1) begin
					spi_read_crm_data_packets_seq read_crm_seq;
					spi_read_pdcm_frame_seq read_pdcm_seq;
					next_frame.update_frame_data_in();
					next_frame.update_sequences();
					
					if($cast(read_crm_seq, next_frame.commands[$-1]) == 1) begin
						spi_read_crm_port.write(read_crm_seq);
					end
					if($cast(read_pdcm_seq, next_frame.commands[$-1]) == 1) begin
						spi_read_pdcm_port.write(read_pdcm_seq);
					end
				end
				
				if(is_crc_command || is_reset_command) begin
					next_frame.update_status();
					next_frame.update_sequences();
					next_frame.sample_cov();
					spi_command_frame_port.write(next_frame);
					end_tr(next_frame);
					frame_started = 1'b0;
					
					data_in.delete();
					data_out.delete();
					next_frame = new();
				end
			end
		end
	endfunction
	
	static function logic[15:0] create_compare_mask(int bit_count);
		return ((2**bit_count)-1) << (16-bit_count);
	endfunction
	
	/**
	 * Check if next command is a "Reset command".
	 */
	static function bit handle_reset_command(spi_seq next_command);
		spi_reset_seq reset_seq;
		if($cast(reset_seq, next_command) == 1) begin
			return ~reset_seq.incomplete;
		end
		return 1'b0;
	endfunction
	
	/**
	 * Check if next command is a "SPI frame CRC command".
	 * If is is: re-calculate mosi and miso CRC
	 */
	static function bit handle_tx_crc_command(spi_command_frame_seq frame, spi_seq next_command, logic[15:0] mask);
		spi_tx_crc_request_seq tx_crc_seq;
		if($cast(tx_crc_seq, next_command) == 1) begin
			logic[15:0] temp_data_in[$]  = frame.crc_data_in;
			logic[15:0] temp_data_out[$] = frame.data_out;
			logic[15:0] calculated_mosi_crc;
			logic[15:0] calculated_miso_crc;
			
			temp_data_in.push_back(tx_crc_seq.data_in[0]);
			temp_data_out.push_back(tx_crc_seq.data_out[0]);
			calculated_mosi_crc = crc_calculation_pkg::spi_calculate_correct_crc(temp_data_in);
			calculated_miso_crc = crc_calculation_pkg::spi_calculate_correct_crc(temp_data_out);
			
			tx_crc_seq.mosi_crc_enable = 0; // do not re-calculate mosi CRC during frame.add_command(...)
			tx_crc_seq.mosi_crc_correct = (calculated_mosi_crc == tx_crc_seq.mosi_crc);
			tx_crc_seq.miso_crc_correct = (calculated_miso_crc == tx_crc_seq.miso_crc);
			
			if(checker_config::get().enable_spi_miso_crc_check == 1'b1) begin
				if((calculated_miso_crc & mask) != (tx_crc_seq.miso_crc & mask)) begin
					frame.uvm_report_error ("spi_protocol_listener", $sformatf("received wrong MISO CRC value, expected 0x%04h, got 0x%04h.", calculated_miso_crc, tx_crc_seq.miso_crc), UVM_NONE, `uvm_file, `uvm_line, "", 1);
				end
			end
			return 1'b1;
		end
		return 1'b0;
	endfunction
	
	`define register_command(_cmd_coding_, _cmd_sequence_class_) if(next_command == null) begin \
																	_cmd_sequence_class_ seq = new(); \
																	if(seq.starts_with(cmd) && seq.create_from(data_in, data_out)) begin \
																		next_command = seq; \
																	end \
																end
	
	/**
	 * Tries to create a spi_seq from given input/output SPI word queue.
	 */
	static function spi_seq create_command(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		logic[15:0] cmd = data_in[0];
		spi_seq next_command;
		
		`register_command (CMD_STATUS_READ		  ,spi_read_status_seq)
		`register_command (CMD_REG_WRITE  		  ,spi_write_master_register_seq)
		`register_command (CMD_REG_READ   		  ,spi_read_master_register_seq)
		`register_command (CMD_CRM       		  ,spi_crm_seq)
		`register_command (CMD_PDCM       		  ,spi_pdcm_seq)
		`register_command (CMD_DSI_DISCOVERY_MODE ,spi_discovery_mode_seq)
		`register_command (CMD_UPLOAD_TDMA		  ,spi_upload_tdma_packet_seq)
		`register_command (CMD_UPLOAD_TDMA		  ,spi_validate_tdma_scheme_seq)
		`register_command (CMD_READ_CRM_PACKETS	  ,spi_read_crm_data_packets_seq)
		`register_command (CMD_READ_PDCM_PACKETS  ,spi_read_pdcm_frame_seq)
		`register_command (CMD_TX_CRC			  ,spi_tx_crc_request_seq)
		`register_command (CMD_DSI_WAIT			  ,spi_dsi_wait_seq)
		`register_command (CMD_DSI_SYNC			  ,spi_sync_dsi_channels_seq)
		`register_command (CMD_DSI_CLEAR_QUEUE	  ,spi_clear_dsi_command_queue_seq)
		`register_command (CMD_DSI_CLEAR_BUF	  ,spi_clear_dsi_data_buffers_seq)
		`register_command (CMD_MEASURE_CURRENT    ,spi_measure_quiescent_current_seq)
		`register_command (CMD_RESET			  ,spi_reset_seq)
		
		return next_command;
	endfunction
endclass


