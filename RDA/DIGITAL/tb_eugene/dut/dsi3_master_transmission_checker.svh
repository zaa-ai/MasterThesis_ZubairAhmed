
class buffer_data_packet extends flags_container #(dsi_response_flags);
	
	int symbol_count;
	logic[15:0] data[$];
	
	// don't check TE flag, a timing occurred where TE may be so or may not be set   
	bit ignore_timing_error_flag;
	// when this packet has been received 
	time packet_receive_time;
	
	function new(string name = "buffer data packet");
		super.new(name);
	endfunction
	
endclass

class pdcm_data_frame extends flags_container #(pdcm_frame_header_flags);
	
	int packet_count;
	// all packets of this frame have been received
	bit frame_finished = 1'b0;
	time frame_finished_time;
	buffer_data_packet packets[$];
	
	function new(string name = "PDCM frame");
		super.new(name);
	endfunction
endclass


typedef enum {
	// nothing to do, wait for next command
	IDLE,
	// running PDCM
	PDCM,
	// wait for expected CRM master transmission
	WAIT_FOR_CRM,
	// running CRM
	CRM,
	// running Discovery Mode
	DM,
	// measure current
	MEASURE,
	// waiting
	WAIT, 
	// waiting for synchronization
	SYNC, 
	// channel has been switched off
	INACTIVE
} checker_state_e;

typedef struct {
	int index;
	bit timing_error;
	bit gray_zone_timing;
} packet_index_t;

// gray zone timing for PDCM 
localparam shortint unsigned PDCM_TIMING_TOLERANCE = 2; 

/**
 * Class: dsi3_master_transmission_checker
 */
class dsi3_master_transmission_checker extends uvm_subscriber #(spi_command_frame_seq);
	
	`uvm_component_utils (dsi3_master_transmission_checker)
	
	uvm_analysis_imp_dsi3_master_tr #(dsi3_master_tr, 	 			dsi3_master_transmission_checker) dsi3_master_export;
	uvm_analysis_imp_dsi3_slave_tr	#(dsi3_slave_tr, 	 			dsi3_master_transmission_checker) dsi3_slave_export;
	uvm_analysis_imp_resb			#(digital_signal_tr, 			dsi3_master_transmission_checker) resb_export;
	uvm_analysis_imp_rfc			#(digital_signal_tr, 			dsi3_master_transmission_checker) rfc_export;
	uvm_analysis_imp_configuration  #(dsi3_master_configuration_tr, dsi3_master_transmission_checker) configuration_export;
	
	common_env_pkg::dsi3_master_configuration_subscriber configuration_subscriber;
	dsi3_transaction_recorder transaction_recorder;
	edf_parameter_model edf_parameters;
	simulation_logger logger;
	
	int	channel = 0;
	bit rfc = 1'b0;
	// physical layer transceiver enable of this channel
	bit dsi_enable = 1'b1;
	
	uvm_tlm_analysis_fifo #(spi_dsi_command_seq) command_queue;
	checker_state_e state;
		
	int period_index;
	bit infinite_pdcm = 1'b0;
	event next_pdcm_period;
	time last_pdcm_pulse_start_time = 0;
	pdcm_data_frame pdcm_buffer[$];
	
	time last_crm_start_time = 0;
	int last_CRM_TIME;
	int last_CRM_TIME_NR;
	bit crm_response_expected = 1'b1; 
	spi_crm_seq last_crm_request;
	buffer_data_packet crm_buffer[$];
	
	int wait_time = 0;
	time last_clear_command_queue_start_time = 0;
	time last_clear_crm_data_buffer_time = 0;
	time last_clear_pdcm_data_buffer_time = 0;
	bit external_sync_received = 1'b0;
	
	int dm_pulse_count = 0;
	time last_dm_pulse_start_time = 0;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		dsi3_master_export = new("dsi3_master_export", this);
		dsi3_slave_export = new("dsi3_slave_export", this);
		resb_export = new("resb_export", this);
		rfc_export = new("rfc_export", this);
		configuration_export = new("configuration_export", this);
		
		command_queue = new("command_queue", this);
		configuration_subscriber = new("transmission_checker_configuration_subscriber", this);
		logger = new("transmission_checker_sim_logger");
	endfunction

	virtual function bit is_enabled();
		return is_reading_enabled() && dsi_enable == 1'b1;
	endfunction
	
	virtual function bit is_reading_enabled();
		return checker_config::get().enable_master_transmission_checker[channel] == 1'b1 && rfc == 1'b1;
	endfunction
	
	function void set_channel(int ch);
		this.channel = ch;		
	endfunction

	function void reset_checker();
		crm_buffer.delete();
		pdcm_buffer.delete();
		command_queue.flush();
		state = IDLE;
		
		period_index = 0;
		infinite_pdcm = 1'b0;
		last_pdcm_pulse_start_time = 0;
		
		last_crm_request = null;
		last_crm_start_time = 0;
		crm_response_expected = 1'b0;
		
		last_clear_command_queue_start_time = 0;
	endfunction
	
	function dsi3_pkg::dsi3_bit_time_e get_bit_time();
		return configuration_subscriber.get_bit_time();
	endfunction
	
	function int get_chip_time();
		return configuration_subscriber.get_chip_time();
	endfunction

	task run_phase(uvm_phase phase);
		run_checker();
	endtask
	
	// a new SPI command frame has been received
	virtual function void write(spi_command_frame_seq t);
		spi_dsi_command_seq valid_commands[$];
		
		if(is_reading_enabled()) begin
			check_status_word(t.status, t.get_begin_time());
		end

		foreach(t.commands[i]) begin
			spi_dsi_command_seq dsi_command;
			spi_read_crm_data_packets_seq read_crm_seq;
			spi_read_pdcm_frame_seq read_pdcm_seq;
			spi_read_dsi_data_seq read_command;
			spi_read_status_seq read_status;
			
			spi_tx_crc_request_seq crc_seq;		
			
			// check if its a (none-read) DSI command for this channel
			if($cast(dsi_command, t.commands[i]) == 1 && $cast(read_command, t.commands[i]) == 0) begin
				if(dsi_command.channel_bits[channel] == 1'b1) begin
					valid_commands.push_back(dsi_command);
				end
			end
			else if($cast(read_crm_seq, t.commands[i]) == 1 && is_reading_enabled()) begin
				handle_read_crm_data_command(read_crm_seq);
			end
			else if($cast(read_pdcm_seq, t.commands[i]) == 1 && is_reading_enabled()) begin
				handle_read_pdcm_frame_command(read_pdcm_seq);
			end
			// read status/NOP command
			else if($cast(read_status, t.commands[i]) == 1 && is_reading_enabled()) begin
				handle_read_status_command(read_status);
			end
			// CRC command
			else if($cast(crc_seq, t.commands[i]) == 1 && is_enabled()) begin
				if(crc_seq.mosi_crc_correct == 1'b1) begin
					// if CRC is correct -> put all commands into queue
					foreach(valid_commands[k]) begin
						spi_clear_dsi_command_queue_seq clear_command_seq;
						spi_clear_dsi_data_buffers_seq  clear_buffers_seq;
						// clear command queue
						if($cast(clear_command_seq, valid_commands[k]) == 1) begin
							handle_clear_command_queue_command(clear_command_seq);
						end
						// clear data buffer
						else if($cast(clear_buffers_seq, valid_commands[k]) == 1) begin
							handle_clear_data_buffer_command(clear_buffers_seq);
						end
						// all queued commands
						else begin
							command_queue.write(valid_commands[k]);
						end
					end
				end
				valid_commands.delete();
			end
		end
	endfunction
	
	
	function void check_status_word(spi_status_word	status, time status_time);
		checker_config cfg = checker_config::get();
		if(cfg.enable_status_word_check == 1'b1) begin 
			// check for HE errors
			if(cfg.enable_hardware_error_check == 1'b1) begin
				if(status.get_value(HE) == 1'b1) `uvm_error(this.get_name(), "HE flag in status word found")
			end
			// TODO: BF is currently not checked (this is difficult because BF is a sum of channel 0/1, CRM/PDCM and SPI command buffer)
			// NT
			check_nt_flag(status, (channel == 0) ? NT0 : NT1);
			// PD
			check_pd_flag(status, (channel == 0) ? PD0 : PD1);
			// CR
			check_cr_flag(status, status_time, (channel == 0) ? CR0 : CR1);
		end
	endfunction
	
	function void check_pd_flag(spi_status_word	status, spi_status_word_flags flag);
		time now = $time();
		bit pdcm_buffer_readable;
		//✅ Injected Human Error: mistakenly clear PDCM buffer before checking
		if (status.get_value(flag) == 1'b1) begin
			pdcm_buffer.delete(); // Mistake: this should NOT be done here — simulates early cleanup
		end
		pdcm_buffer_readable = pdcm_buffer.size() > 1 || (pdcm_buffer.size() > 0 && pdcm_buffer[$].frame_finished == 1'b1);
		// bit pdcm_buffer_readable = pdcm_buffer.size() > 1 || (pdcm_buffer.size() > 0 && pdcm_buffer[$].frame_finished == 1'b1);
		// time now = $time();
		if(status.get_value(flag) == 1'b1) begin
			if(pdcm_buffer_readable == 1'b0) begin
				time davail_time = edf_parameters.epms.t__CRM_davail__.get_max_time(); // also use t__CRM_davail__ here, because there is no such time for PDCM
				time time_since_last_clear = now - last_clear_pdcm_data_buffer_time;	
				if(time_since_last_clear > 0 && time_since_last_clear < davail_time) begin
					`uvm_info(this.get_name(), $sformatf("ignored PD%0d flag in status word, because of gray zone timing between status read and last clear buffer command", channel), UVM_MEDIUM)
				end
				else begin
					`uvm_error(this.get_name(), $sformatf("PD%0d flag in status word found, but no data is expected to be contained in PDCM buffer of channel %0d", channel, channel))
				end
			end
		end
		else begin
			if(pdcm_buffer_readable == 1'b1) begin
				time buffer_finished = pdcm_buffer[0].frame_finished_time;
				// gray zone +/- 5us around a finished buffer
				if(buffer_finished > now - 5us && buffer_finished < now + 5us) begin
					`uvm_info(this.get_name(), $sformatf("ignored PD%0d flag in status word, because of gray zone timing between read PDCM and end of last PDCM period", channel), UVM_MEDIUM)
				end
				else begin
					`uvm_error(this.get_name(), $sformatf("no PD%0d flag in status word found, but there seems to be data contained in PDCM buffer of channel %0d", channel, channel))
				end
			end
		end
	endfunction

	function void check_cr_flag(spi_status_word	status, time status_time, spi_status_word_flags flag);
		bit crm_buffer_readable = crm_buffer.size() > 0;
		time davail_time = edf_parameters.epms.t__CRM_davail__.get_max_time();

		if(status.get_value(flag) == 1'b1) begin
			if(crm_buffer_readable == 1'b0) begin
				time time_since_last_clear = $time() - last_clear_crm_data_buffer_time;	
				if(time_since_last_clear > 0 && time_since_last_clear < davail_time) begin
					`uvm_info(this.get_name(), $sformatf("ignored CR%0d flag in status word, because of gray zone timing between status read and last clear buffer command", channel), UVM_MEDIUM)
				end
				else begin
					`uvm_error(this.get_name(), $sformatf("CR%0d flag in status word found, but no data is expected to be contained in CRM buffer of channel %0d", channel, channel))
				end
			end
		end
		else begin
			if(crm_buffer_readable == 1'b1) begin
				time receive_time =	crm_buffer[0].packet_receive_time;
				// if status has been requested before buffer packet has been received or if status request is before end of t__CRM,davail__ -> ignore
				if(status_time <= receive_time || status_time - receive_time < davail_time) begin
					`uvm_info(this.get_name(), $sformatf("ignored CR%0d flag in status word, because of gray zone timing between status read and reception of DSI data", channel), UVM_MEDIUM)
				end
				else begin				
					`uvm_error(this.get_name(), $sformatf("no CR%0d flag in status word found, but there seems to be data contained in CRM buffer of channel %0d", channel, channel))
				end
			end
		end
	endfunction
	
	function void check_nt_flag(spi_status_word	status, spi_status_word_flags flag);
		if(status.get_value(flag) == 1'b1) begin
			if(tdma_scheme_upload_listener::schemes[channel].valid == 1'b1) begin
				`uvm_error(this.get_name(), $sformatf("NT%0d flag in status word found, but there is a valid TDMA scheme, expected NT%0d not to be set", channel, channel))
			end
		end
		else begin
			if(tdma_scheme_upload_listener::schemes[channel].valid == 1'b0) begin
				`uvm_error(this.get_name(), $sformatf("no NT%0d flag in status word found, but there is a no valid TDMA scheme, expected NT%0d to be set", channel, channel))
			end
		end
	endfunction

	// Received a DSI3 master transaction.
	function void write_dsi3_master_tr(dsi3_master_tr t);
		transaction_recorder.received_master_tr(channel, t);
		if (is_enabled()) begin
			// any external sync seems to be over
			external_sync_received = 1'b0;
			// PDCM
			if(t.msg_type == dsi3_pkg::PDCM) begin
				received_master_transaction_pdcm(t);
			end
			// CRM
			else if(t.msg_type == dsi3_pkg::CRM) begin
				received_master_transaction_crm(t);
			end
			// Discovery Mode
			else if(t.msg_type == dsi3_pkg::DM) begin
				received_master_transaction_dm(t);
			end
		end
	endfunction
	
	/**
	 * Received a DSI3 slave transaction.
	 */
	function void write_dsi3_slave_tr(dsi3_slave_tr t);
		
		// discovery mode
		if(state == DM && t.msg_type == dsi3_pkg::DM) begin
			if(last_dm_pulse_start_time != 0) begin
				edf_parameter_base param = get_t__Disc_dly();
				time delay = t.get_begin_time() - last_dm_pulse_start_time;
				logger.log_sim_measure(param.get_name(), $sformatf("%0f", delay / 1.0us), $sformatf("at channel %0d", channel));
			end
			return;
		end
		
		// ignore less than 4 symbols	
		if(t.data.size() < 4) begin
			return;
		end
		
		// PDCM pending
		if(state == PDCM) begin
			if(pdcm_buffer.size() == 0) begin
				`uvm_error(this.get_name(), "unexpected PDCM slave transaction, checker is not in PDCM state")
			end
			else begin
				int buffer_index = pdcm_buffer[$].packets.size();
				if(buffer_index < tdma_scheme_upload_listener::schemes[channel].get_packet_count()) begin
					packet_index_t tdma_index = find_index_from_tdma_scheme(buffer_index, t);
					if(tdma_index.index != -1) begin
						tdma_scheme_packet next_tdma_packet = tdma_scheme_upload_listener::schemes[channel].packets[tdma_index.index];
						dsi3_pkg::sid_length_e source_id = next_tdma_packet.id_symbol_count;
						dsi3_pdcm_packet dsi_packet = dsi3_pdcm_packet::create_packet(t.data, source_id);
						buffer_data_packet buffer_packet = create_buffer_packet(dsi_packet, next_tdma_packet.symbol_count);
						buffer_packet.ignore_timing_error_flag = tdma_index.gray_zone_timing;
						if(t.data.size() > 255 || buffer_packet.symbol_count != next_tdma_packet.symbol_count) buffer_packet.set_flags({SCE});
						if(tdma_index.timing_error == 1'b1) buffer_packet.set_flags({TE});
						pdcm_buffer[$].packets.push_back(buffer_packet);
					end
					else begin
						`uvm_error(this.get_name(), "failed to find a matching slot/index for packet within TDMA scheme (something went wrong)")
					end
				end
				// ignore slave transactions that do not fit into TDMA scheme
				else begin
					pdcm_buffer[$].set_flags({PC});			
				end
				pdcm_buffer[$].packet_count += 1;
			end
		end
		else begin
			time start_time = t.get_begin_time() - last_crm_start_time;
			int t_crm_answer = int'(start_time / 1us);
			dsi3_pkg::dsi3_bit_time_e bit_time = get_bit_time();
			int bittime_factor = dsi3_pkg::get_bit_time_factor(bit_time);
			
			// t__CRM,answer,low to t__CRM,answer,high
			if(crm_response_expected == 1'b1 && last_crm_request != null && last_crm_request.broad_cast == 1'b0 && t_crm_answer >= (256*bittime_factor) && t_crm_answer <= last_CRM_TIME) begin
				dsi3_crm_packet dsi_packet = dsi3_crm_packet::create_packet(t.data);
				buffer_data_packet buffer_packet = create_buffer_packet(dsi_packet);
				edf_parameter t__CRM_answer_low = get_t__CRM_answer_low();
				edf_parameter t__CRM_answer_high = get_t__CRM_answer_high();
				// check symbol count
				if(buffer_packet.symbol_count != 'd8) begin
					buffer_packet.set_flags({SCE});
				end
				// TE flag has to be set
				if(t_crm_answer < t__CRM_answer_low.get_min_as_int() || t_crm_answer > t__CRM_answer_high.get_max_as_int()) begin
					buffer_packet.set_flags({TE});
				end
				// ignore TE flag (lower gray area)
				else if(t_crm_answer >= t__CRM_answer_low.get_min_as_int() && t_crm_answer <= t__CRM_answer_low.get_max_as_int()) begin
					buffer_packet.ignore_timing_error_flag = 1'b1;
				end
				// ignore TE flag (upper gray area)
				else if(t_crm_answer >= t__CRM_answer_high.get_min_as_int() && t_crm_answer <= t__CRM_answer_high.get_max_as_int()) begin
					buffer_packet.ignore_timing_error_flag = 1'b1;
				end
				apply_expected_CRM_error_flags(buffer_packet);
				
				crm_buffer.push_back(buffer_packet);
				crm_response_expected = 1'b0;
			end
			else begin
				if(is_enabled()) begin
					`uvm_info(this.get_name(), $sformatf("ignored unexpected slave response"), UVM_MEDIUM)
				end
			end
		end
		
		transaction_recorder.received_slave_tr(channel, t);
	endfunction
	
	function edf_parameter get_t__CRM_answer_low();
		case (get_bit_time())
			dsi3_pkg::BITTIME_8US : return edf_parameters.epms.t__CRM_answer_low_8__;
			dsi3_pkg::BITTIME_16US: return edf_parameters.epms.t__CRM_answer_low_16__;
			dsi3_pkg::BITTIME_32US: return edf_parameters.epms.t__CRM_answer_low_32__;
		endcase
		return null;
	endfunction
	
	function edf_parameter get_t__CRM_answer_high();
		case (get_bit_time())
			dsi3_pkg::BITTIME_8US : return edf_parameters.epms.t__CRM_answer_high_8__;
			dsi3_pkg::BITTIME_16US: return edf_parameters.epms.t__CRM_answer_high_16__;
			dsi3_pkg::BITTIME_32US: return edf_parameters.epms.t__CRM_answer_high_32__;
		endcase
		return null;
	endfunction
	
	// discovery mode pulse period
	function edf_parameter_base get_t__Disc_per();
		case (get_bit_time())
			dsi3_pkg::BITTIME_8US : return edf_parameters.epms.t__Disc_per_8__;
			dsi3_pkg::BITTIME_16US: return edf_parameters.epms.t__Disc_per_16__;
			dsi3_pkg::BITTIME_32US: return edf_parameters.epms.t__Disc_per_32__;
		endcase
		return null;
	endfunction

	// discovery mode slave response current delay time
	function edf_parameter_base get_t__Disc_dly();
		case (get_bit_time())
			dsi3_pkg::BITTIME_8US : return edf_parameters.epms.t__Disc_dly_valid_8__;
			dsi3_pkg::BITTIME_16US: return edf_parameters.epms.t__Disc_dly_valid_16__;
			dsi3_pkg::BITTIME_32US: return edf_parameters.epms.t__Disc_dly_valid_32__;
		endcase
		return null;
	endfunction
	
	// go through all TDMA packets and find a matching packet/slot 
	function packet_index_t find_index_from_tdma_scheme(int buffer_index, dsi3_slave_tr t);
		packet_index_t result;
		tdma_scheme_pdcm scheme = tdma_scheme_upload_listener::schemes[channel];
		shortint unsigned packet_start = shortint'((t.get_begin_time() - last_pdcm_pulse_start_time) / 1us);
		int tdma_packet_count = scheme.get_packet_count();
		for (int i = buffer_index; i < tdma_packet_count; i++) begin
			tdma_scheme_packet next_tdma_packet = scheme.packets[i];
			result.index = i;
			result.gray_zone_timing = is_gray_zone_timing(packet_start, next_tdma_packet);
			if(next_tdma_packet.enable == 1'b1) begin
				// perfect match
				if(next_tdma_packet.earliest_start_time <= packet_start && packet_start <= next_tdma_packet.latest_start_time) begin
					result.timing_error = 1'b0;
					return apply_period_end_timing_error(result, t, scheme);;
				end
				// packet was too early
				if(packet_start < next_tdma_packet.earliest_start_time) begin
					result.timing_error = 1'b1;
					return result;
				end
				// packet was too late
				if(i < tdma_packet_count - 1) begin
					tdma_scheme_packet following_tdma_packet = scheme.packets[i+1];
					if(following_tdma_packet.enable == 1'b1) begin
						shortint unsigned latest_tolerance_time = shortint'(next_tdma_packet.latest_start_time + (following_tdma_packet.earliest_start_time - next_tdma_packet.latest_start_time) / 2);
						if(packet_start < latest_tolerance_time) begin
							result.timing_error = 1'b1;
							return result;
						end
					end
				end
				// it's the last packet within TDMA scheme
				if(i == tdma_packet_count - 1) begin
					result.timing_error = 1'b1;
					return result;
				end
				// no match -> insert an empty packet
				insert_empty_pdcm_packet_to_buffer(next_tdma_packet);
			end
			else begin
				break;
			end
		end
		result.index = -1;
		result.timing_error = 1'b1;
		return result;
	endfunction
	
	function bit is_gray_zone_timing(shortint unsigned packet_start, tdma_scheme_packet next_tdma_packet);
		if(packet_start >= next_tdma_packet.earliest_start_time - PDCM_TIMING_TOLERANCE && packet_start <= next_tdma_packet.earliest_start_time + PDCM_TIMING_TOLERANCE) begin
			return 1'b1;
		end
		if(packet_start >= next_tdma_packet.latest_start_time - PDCM_TIMING_TOLERANCE && packet_start <= next_tdma_packet.latest_start_time + PDCM_TIMING_TOLERANCE) begin
			return 1'b1;
		end
		return 1'b0;
	endfunction
	
	// checks for TE or gray zone at end of PDCM period 
	function packet_index_t apply_period_end_timing_error(packet_index_t result, dsi3_slave_tr t, tdma_scheme_pdcm scheme);
		time period_end_time = last_pdcm_pulse_start_time + (scheme.pdcm_period * 1us) - 10us; // -10us receive timeout
		
		if(t.get_end_time() >= period_end_time) begin
			result.timing_error = 1'b1;
		end
		else begin
			int chip_time = get_chip_time();
			time diff = period_end_time - t.get_end_time();
			if(diff < (3 * chip_time * 1us)) begin
				result.timing_error = 1'b1;
			end 
			else if(diff < (6 * chip_time * 1us)) begin
				result.gray_zone_timing = 1'b1;
			end
		end
		return result;
	endfunction
	
	function void insert_empty_pdcm_packet_to_buffer(tdma_scheme_packet next_tdma_packet);
		buffer_data_packet empty_packet;
		dsi3_pdcm_packet dsi_packet;
		logic[3:0] empty_data[$];
		repeat(next_tdma_packet.symbol_count) empty_data.push_back(4'h0);
		dsi_packet = dsi3_pdcm_packet::create_packet(empty_data, next_tdma_packet.id_symbol_count);
		empty_packet = create_buffer_packet(dsi_packet);
		empty_packet.symbol_count = 'd0;
		empty_packet.set_flags({SCE});
		empty_packet.set_value(CRC, 1'b0); // make sure there is no CRC flag for this empty packet
		pdcm_buffer[$].packets.push_back(empty_packet);
	endfunction
	
	function buffer_data_packet create_buffer_packet(dsi3_packet dsi_packet, int expected_symbol_count = -1);
		buffer_data_packet buffer_packet = new();
		buffer_packet.packet_receive_time = $time();
		// remove data greater than 256 symbols
		while(dsi_packet.data.size() > 256) begin
			dsi_packet.data.pop_back();
		end
		// replace 'hx by 'h0 (e.g. there was a symbol coding error)
		foreach(dsi_packet.data[i]) begin
			if(dsi_packet.data[i] === 4'hx) begin
				dsi_packet.data[i] = 4'h0;
			end
		end
		buffer_packet.symbol_count = (dsi_packet.data.size() > 255) ? 255 : dsi_packet.data.size();
		if (convert_queue#(4, 16)::convert(dsi_packet.data, buffer_packet.data, 1)) `uvm_error(this.get_name(), "failed to convert queue of expected data")
		
		// remove unexpected symbols before CRC is calculated
		if(expected_symbol_count > 0) begin
			while(dsi_packet.data.size() > expected_symbol_count) begin
				dsi_packet.data.pop_back();
			end
		end
		if(dsi_packet.check_crc() == 1'b0) buffer_packet.set_flags({CRC});
		return buffer_packet;
	endfunction
	
	function buffer_data_packet create_empty_buffer_packet(int word_count);
		buffer_data_packet packet = new();
		packet.symbol_count = 0;
		repeat (word_count) begin
			packet.data.push_back(16'h0);
		end
		return packet;
	endfunction
		
	// reset (RESB pin) -> clear all buffers
	function void write_resb(digital_signal_tr t);
		reset_checker();
	endfunction
	
	// state change at RFC pin
	function void write_rfc(digital_signal_tr t);
		rfc = t.value;		
	endfunction
	
	// new DSI configuration has been written
	function void write_configuration(dsi3_master_configuration_tr t);
		if(dsi_enable == 1'b1 && t.dsi_enable[channel] == 1'b0) begin
			// clear command queue
			command_queue.flush();
			period_index = 0;
			infinite_pdcm = 1'b0;
			last_pdcm_pulse_start_time = 0;
			
			last_crm_request = null;
			last_crm_start_time = 0;
			crm_response_expected = 1'b0;
			last_clear_command_queue_start_time = 0;
			
			last_dm_pulse_start_time = 0;
			dm_pulse_count = 0;
			
			// clear data of current PDCM frame
			if(state == PDCM && pdcm_buffer.size() > 0 && pdcm_buffer[$].frame_finished == 1'b0) begin
				pdcm_buffer.pop_back();
			end
			// running CRM and response has already been received -> clear it
			if(state == CRM && crm_buffer.size() > 0 && last_crm_request != null && last_crm_request.broad_cast == 1'b0 && crm_response_expected == 1'b0) begin
				crm_buffer.pop_back();				
			end
			// a command in execution is aborted immediately
			state = IDLE;
		end
		dsi_enable = t.dsi_enable[channel];
	endfunction
	
	
	function void received_master_transaction_pdcm(dsi3_master_tr t);
		time pulse_start_time = t.get_begin_time();
		time pulse_end_time = t.get_end_time();
		time pulse_width_time = pulse_end_time - pulse_start_time;
		
		time clear_accept_start_time = pulse_start_time - 10us; // 10us is just an arbitrary gray zone tolerance 
		time clear_accept_end_time = pulse_end_time + pulse_width_time + 10us;
		 
		if(last_clear_command_queue_start_time > clear_accept_start_time && last_clear_command_queue_start_time < clear_accept_end_time) begin
			// there was a "Clear Command Queue" within the PDCM pulse: so go back to PDCM mode
			state = PDCM;
			// this is a little "hack" to get checker state machine back into PDCM mode
			fork
				#1ns;
				infinite_pdcm = 1'b0;
				period_index = 0;
				-> next_pdcm_period;
			join_none
		end
		
		if(state != PDCM) begin
			if(tdma_scheme_upload_listener::schemes[channel].valid == 1'b0) begin
				`uvm_error(this.get_name(), "got unexpected PDCM pulse without a valid TDMA scheme")
			end 
			else begin
				`uvm_error(this.get_name(), $sformatf("got PDCM pulse without SPI request"))
			end
		end
		else begin
			if(checker_config::get().enable_measure_pdcm_pulse == 1'b1) begin
				measure_pdcm_pulse(t);
			end
			
			create_new_pdcm_frame(t);	
			measure_pdcm_period(t);
			
			last_pdcm_pulse_start_time = t.get_begin_time();
			
			// insert possibly missing packets at the end (receive timeout) of this period
			fork
				begin
					time current_time = $time();
					time period_end = last_pdcm_pulse_start_time + (tdma_scheme_upload_listener::schemes[channel].pdcm_period * 1us) - 10us; // 10us -> receive timeout
					if(current_time < period_end) begin
						#(period_end - current_time);
						finalize_pdcm_buffer();
					end
				end
			join_none
			
			if(infinite_pdcm == 1'b0 && period_index > 0) begin
				period_index--;
			end
			-> next_pdcm_period;
		end
	endfunction
	
	function void received_master_transaction_crm(dsi3_master_tr t);
		bit stop_during_crm_transmission = 1'b0;
		// check if there was a clear command queue SPI command during CRM transmission
		if(last_clear_command_queue_start_time > t.get_begin_time() && last_clear_command_queue_start_time < t.get_end_time()) begin
			stop_during_crm_transmission = 1'b1;
		end
		
		if(state == WAIT_FOR_CRM || stop_during_crm_transmission == 1'b1) begin
			crm_response_expected = last_crm_request.broad_cast == 1'b0;
			last_crm_start_time = t.get_begin_time();
			
			if(t.data.size() != 32) begin
				`uvm_error(this.get_name(), $sformatf("unexpected number of data in CRM transmission, expected 32, got %0d bits", t.data.size()));
			end
			else begin
				logic[3:0] symbol_data[$];
				convert_queue#(1, 4)::convert(t.data, symbol_data, 1); // master transaction contains data as single bits
				
				if(configuration_subscriber.crc_en == 1'b1) begin
					// calculate a correct CRC for comparison
					last_crm_request.crm_packet.crc_correct = 1'b1;
					last_crm_request.crm_packet.update_crc();
				end
				foreach(symbol_data[i]) begin
					if(symbol_data[i] != last_crm_request.crm_packet.data[i]) begin
						`uvm_error(this.get_name(), $sformatf("unexpected data in CRM transmission at index %0d, expected %1h, got %1h", i, last_crm_request.crm_packet.data[i], symbol_data[i]));
					end
				end
			end
			
			state = CRM;
		end
		else begin
			`uvm_error(this.get_name(), $sformatf("got CRM transmission without SPI request"))
		end
	endfunction

	function void received_master_transaction_dm(dsi3_master_tr t);
		if(state == DM) begin
			if(checker_config::get().enable_measure_discovery_pulse == 1'b1) begin
				measure_discovery_pulse(t);
			end
			
			if(last_dm_pulse_start_time != 0) begin
				edf_parameter param = get_t__Disc_per();
				time period = t.get_begin_time() - last_dm_pulse_start_time;
				logger.log_sim_measure(param.get_name(), $sformatf("%0f", period / 1.0us), $sformatf("at channel %0d", channel));
			end
			last_dm_pulse_start_time = t.get_begin_time();
			dm_pulse_count++;
		end
		else begin
			`uvm_error(this.get_name(), $sformatf("got DM transmission without SPI request"))
		end
	endfunction
	
	// inserts an empty CRM packet with set SCE flag into CRM data buffer.	
	function void add_empty_crm_packet_to_buffer();
		dsi3_crm_packet dsi_packet = dsi3_crm_packet::get_from_queue({16'h0000, 16'h0000});
		buffer_data_packet buffer_packet = create_buffer_packet(dsi_packet);
		buffer_packet.symbol_count = 'd0;
		buffer_packet.set_value(SCE, 1'b1);
		buffer_packet.set_value(CRC, 1'b0);
		apply_expected_CRM_error_flags(buffer_packet);
		crm_buffer.push_back(buffer_packet);
	endfunction
	
	function void apply_expected_CRM_error_flags(buffer_data_packet buffer_packet);
		checker_config _config = checker_config::get();
		if(_config.expect_CRM_clock_ref_error_in_dsi_packet == 1'b1) begin
			buffer_packet.set_flags({CE});
		end
		if(_config.expect_CRM_voltage_error_in_dsi_packet[channel] == 1'b1) begin
			buffer_packet.set_flags({VE});
		end
		if(_config.expect_CRM_symbol_coding_error_in_dsi_packet[channel] == 1'b1) begin
			buffer_packet.set_flags({SE});
		end
	endfunction
	
	function bit contains_index(int index, int queue[$]);
		int positions[$] = queue.find_first_index( x ) with ( x == index );
		return positions.size() > 0;		
	endfunction
	
	function void measure_pdcm_period(dsi3_master_tr t);
		if(period_index > 0 || infinite_pdcm == 1'b1) begin
			if(last_pdcm_pulse_start_time > 0) begin
				if(checker_config::get().enable_check_pdcm_period == 1'b1) begin
					time measured_period = t.get_begin_time() - last_pdcm_pulse_start_time;
					time expected_period = (tdma_scheme_upload_listener::schemes[channel].pdcm_period) * 1us;
					`uvm_info(get_type_name(), $sformatf("measured PDCM period at channel %0d: %0f us - %0d pulses left", channel, measured_period / 1.0us, period_index-1), UVM_MEDIUM)
					compare_times(expected_period, measured_period, $sformatf("expected PDCM period of channel %0d", channel), 1ns);
				end
			end
		end
	endfunction
	
	function void create_new_pdcm_frame(dsi3_master_tr t);
		pdcm_data_frame frame = new();
		frame.packet_count = 0;
		pdcm_buffer.push_back(frame);
	endfunction
	
	function void measure_pdcm_pulse(dsi3_master_tr t);
		time bit_time = (t.get_end_time() - t.get_begin_time());
		string value = $sformatf("%0f", bit_time / 1.0us);
		string condition = $sformatf("at channel %0d", channel);
		case (get_bit_time())
			dsi3_pkg::BITTIME_16US: begin
				logger.log_sim_measure("t__DSI,BIT,16__", value, condition);
			end
			dsi3_pkg::BITTIME_32US: begin
				logger.log_sim_measure("t__DSI,BIT,32__", value, condition);
			end
			default: begin
				logger.log_sim_measure("t__DSI,BIT,8__", value, condition);
			end
		endcase
	endfunction
	
	function void measure_discovery_pulse(dsi3_master_tr t);
		time duration = (t.get_end_time() - t.get_begin_time());
		string value = $sformatf("%0f", duration / 1.0us);
		string condition = $sformatf("at channel %0d", channel);
		case (get_bit_time())
			dsi3_pkg::BITTIME_16US: begin
				logger.log_sim_measure("t__Disc_pulse,16__", value, condition);
			end
			dsi3_pkg::BITTIME_32US: begin
				logger.log_sim_measure("t__Disc_pulse,32__", value, condition);
			end
			default: begin
				logger.log_sim_measure("t__Disc_pulse,8__", value, condition);
			end
		endcase
	endfunction
	
	task run_checker();
		state = IDLE;
		
		forever begin
			case (state)
				IDLE: begin
					fork
						begin
							spi_dsi_command_seq next_command;
							command_queue.get(next_command);
							handle_next_command(next_command);
						end
						begin
							@state;
						end
					join_any
					disable fork;
				end
				PDCM: begin
					// FIXME: implement timeout -> there was no PDCM pulse but there should be one
					
					fork
						@(state); // state may have changed (e.g. by a disabled DSI channel: DSI_ENABLE.TRE)
						@(next_pdcm_period);
					join_any
					disable fork;	
					
					if(state == PDCM && period_index == 0 && infinite_pdcm == 1'b0) begin
						int pdcm_period_duration = tdma_scheme_upload_listener::schemes[channel].pdcm_period;
						time current_time = $time();
						time period_end = last_pdcm_pulse_start_time + (pdcm_period_duration * 1us) - 10us; // 10us -> receive timeout
						if(current_time < period_end) begin
							// wait for one more period to finish PDCM
							#(period_end - current_time);
						end
						last_pdcm_pulse_start_time = 0;
						state = IDLE;
					end
				end
				WAIT_FOR_CRM: begin
					// wait until master CRM transmission was received or a timeout was hit
					fork
						@state;
						begin
							// timeout for an expected CRM transmission
							if(external_sync_received == 1'b0) begin
								#10ms;
							end else begin
								#100ms; // wait much longer in case of an external sync
							end
							`uvm_error(this.get_name(), "timeout for expected CRM transmission reached, there was no transmission for pending SPI request")
							
						end
					join_any
					disable fork;
					if(state != IDLE && state != CRM) begin
						`uvm_error(this.get_name(), $sformatf("unexpected state after waiting for CRM transmission: WAIT_FOR_CRM -> %s", state.name()))
						state = IDLE;
					end
				end
				CRM: begin
					// wait until configured end of CRM
					int crm_duration = (last_crm_request.broad_cast == 1'b1) ? last_CRM_TIME_NR : last_CRM_TIME;
					time current_time = $time();
					time crm_end = last_crm_start_time + (crm_duration * 1us);
					if(current_time < crm_end) begin
						#(crm_end - current_time);
					end
					// there is still an answer missing
					if(crm_response_expected == 1'b1) begin
						add_empty_crm_packet_to_buffer();
						crm_response_expected = 1'b0;
					end
					state = IDLE;
				end
				DM: begin
					fork
						begin
							// wait for next DM pulse
							@(dm_pulse_count);
						end
						begin
							edf_parameter dm_period = get_t__Disc_per();
							#(dm_period.get_max_as_int() * 1us);							
							state = IDLE;
						end
					join_any
					disable fork;
				end
				MEASURE: begin
					#80us;
					state = IDLE;
				end
				WAIT: begin
					fork
						begin
							#(wait_time * 1us);
						end
						begin
							// by a "clear command queue" command WAIT has to be aborted
							@state;
							if(state != IDLE) begin
								`uvm_error(this.get_name(), $sformatf("unexpected state change from WAIT to %s", state))
								state = IDLE;
							end
						end
					join_any
					disable fork;
					wait_time = 0;
					state = IDLE;
				end
				default: begin
					#1ns;
				end
			endcase
		end
	endtask
	
	function void finalize_pdcm_buffer();
		insert_missing_tdma_scheme_packets();
		apply_expected_PDCM_error_flags();
		check_pdcm_buffer_fill_state();
	endfunction
	
	// insert missing empty packets into PDCM buffer (this is needed if all packets are missing or if last packets are missing)
	// --> there was no subsequent slave transaction that could trigger insertion of empty packets
	function void insert_missing_tdma_scheme_packets();
		if(pdcm_buffer.size() > 0) begin
			int buffer_index = pdcm_buffer[$].packets.size();
			int tdma_packet_count = tdma_scheme_upload_listener::schemes[channel].get_packet_count();
			for (int i = buffer_index; i < tdma_packet_count; i++) begin
				tdma_scheme_packet next_tdma_packet = tdma_scheme_upload_listener::schemes[channel].packets[i];
				insert_empty_pdcm_packet_to_buffer(next_tdma_packet);
			end
			pdcm_buffer[$].frame_finished = 1'b1;
			pdcm_buffer[$].frame_finished_time = $time;
		end
	endfunction
	
	function void apply_expected_PDCM_error_flags();
		if(pdcm_buffer.size() > 0) begin
			checker_config _config = checker_config::get();
			pdcm_data_frame frame = pdcm_buffer[$];	
			foreach(frame.packets[i]) begin
				if(contains_index(i, _config.expect_PDCM_clock_ref_error_in_dsi_packet[channel]) == 1'b1) begin
					frame.packets[i].set_flags({CE});
				end
				if(contains_index(i, _config.expect_PDCM_voltage_error_in_dsi_packet[channel]) == 1'b1) begin
					frame.packets[i].set_flags({VE});
				end
				if(contains_index(i, _config.expect_PDCM_symbol_coding_error_in_dsi_packet[channel]) == 1'b1) begin
					frame.packets[i].set_flags({SE});
				end
			end
		end
	endfunction
	
	// remove last PDCM frame if buffer is already full
	function void check_pdcm_buffer_fill_state();
		int buffer_size = calculate_pdcm_buffer_size();
		if(buffer_size > int'(project_pkg::SIZE_DSI_PDCM_BUF - 16'd1)) begin
			pdcm_buffer.pop_back();
			`uvm_info(get_type_name(), $sformatf("dropped PDCM frame data at channel %0d, buffer is already full", channel), UVM_MEDIUM)					
		end
	endfunction
	
	function int calculate_pdcm_buffer_size();
		int buffer_size = 0;
		foreach(pdcm_buffer[frame_index]) begin
			buffer_size++; // frame header
			foreach(pdcm_buffer[frame_index].packets[packet_index]) begin
				buffer_size++; // packet header
				buffer_size += pdcm_buffer[frame_index].packets[packet_index].data.size(); // words
			end
		end
		return buffer_size;
	endfunction

	function int calculate_crm_buffer_size();
		int buffer_size = 0;
		foreach(crm_buffer[index]) begin
			buffer_size++; // packet header
			buffer_size = crm_buffer[index].data.size(); // words
		end
		return buffer_size;
	endfunction
	
	function void handle_next_command(spi_dsi_command_seq command);
		spi_crm_seq crm_seq;						
		spi_pdcm_seq pdcm_seq;
		spi_discovery_mode_seq dm_seq;
		spi_measure_quiescent_current_seq measure_seq;
		spi_sync_dsi_channels_seq sync_seq;
		spi_upload_tdma_packet_seq upload_tdma_packet_seq;
		spi_validate_tdma_scheme_seq validate_tdma_seq;
		spi_dsi_wait_seq wait_seq;
		
		if(is_enabled()) begin
			// CRM
			if($cast(crm_seq, command) == 1) begin
				handle_crm_command(crm_seq);
			end
			// PDCM
			else if($cast(pdcm_seq, command) == 1) begin
				handle_pdcm_command(pdcm_seq);
			end
			// discovery mode
			else if($cast(dm_seq, command) == 1) begin
				handle_discovery_mode_command(dm_seq);
			end
			// measure current
			else if($cast(measure_seq, command) == 1) begin
				handle_measure_current_command(measure_seq);
			end
			// WAIT
			else if($cast(wait_seq, command) == 1) begin
				handle_wait_command(wait_seq);
			end
			// upload TDMA packet
			else if($cast(upload_tdma_packet_seq, command) == 1) begin
				handle_upload_tdma_packet_command(upload_tdma_packet_seq);
			end
			// validate TDMA scheme
			else if($cast(validate_tdma_seq, command) == 1) begin
				handle_validate_tdma_scheme_command(validate_tdma_seq);
			end
			// sync channels
			else if($cast(sync_seq, command) == 1) begin
				handle_sync_command_command(sync_seq);
			end
			else begin
				`uvm_error(this.get_name(), $sformatf("found unknown/unexpected command in SPI frame: %s", command.convert2string()))
			end
		end
	endfunction
	
	function void handle_crm_command(spi_crm_seq crm_seq);
		last_crm_request = crm_seq;
		last_CRM_TIME    = configuration_subscriber.get_crm_time();
		last_CRM_TIME_NR = configuration_subscriber.get_crm_time_nr();
		state = WAIT_FOR_CRM;
	endfunction
	
	function void handle_pdcm_command(spi_pdcm_seq pdcm_seq);
		tdma_scheme_pdcm scheme = tdma_scheme_upload_listener::schemes[channel];
		if(scheme.valid == 1'b1) begin
			`uvm_info(get_type_name(), $sformatf("start PDCM at channel %0d with %0d pulses and a PDCM period of %0d", channel, pdcm_seq.pulse_count, tdma_scheme_upload_listener::schemes[channel].pdcm_period), UVM_MEDIUM)
			period_index = pdcm_seq.pulse_count;
			infinite_pdcm = pdcm_seq.pulse_count == 8'd0;
			state = PDCM;
		end
	endfunction
	
	function void handle_discovery_mode_command(spi_discovery_mode_seq dm_seq);
		last_dm_pulse_start_time = 0;
		dm_pulse_count = 0;
		state = DM;
	endfunction

	function void handle_measure_current_command(spi_measure_quiescent_current_seq measure_seq);
		state = MEASURE;
	endfunction
	
	function void handle_wait_command(spi_dsi_wait_seq wait_seq);
		wait_time = int'(wait_seq.wait_time);
		state = WAIT;
	endfunction
	
	function void handle_read_status_command(spi_read_status_seq read_status_seq);
		check_status_word(read_status_seq.status, read_status_seq.get_begin_time());
	endfunction
	
	function void handle_upload_tdma_packet_command(spi_upload_tdma_packet_seq upload_tdma_packet_seq);
		pdcm_buffer.delete();
	endfunction
	
	function void handle_validate_tdma_scheme_command(spi_validate_tdma_scheme_seq validate_tdma_seq);
		pdcm_buffer.delete();
	endfunction
	
	// clear command queue
	function void handle_clear_command_queue_command(spi_clear_dsi_command_queue_seq clear_queue_seq);
		command_queue.flush();
		last_clear_command_queue_start_time = $time();
		if(state == WAIT || state == WAIT_FOR_CRM) begin
			state = IDLE;
		end
		else if(state == PDCM) begin
			// clear requested PDCM pulses
			period_index = 0;
			// stop infinite PDCM
			infinite_pdcm = 1'b0;
			-> next_pdcm_period;
		end
	endfunction
	
	// clear data buffer 
	function void handle_clear_data_buffer_command(spi_clear_dsi_data_buffers_seq clear_buffer_seq);
		if(clear_buffer_seq.crm_buffer == 1'b1) begin
			handle_clear_crm_data_buffer();				
		end
		if(clear_buffer_seq.pdcm_buffer == 1'b1) begin
			handle_clear_pdcm_data_buffer();
		end	
	endfunction
	
	function void handle_clear_crm_data_buffer();
		if(state != CRM) begin
			crm_response_expected = 1'b0;
		end
		crm_buffer.delete();
		last_clear_crm_data_buffer_time = $time();
	endfunction
	
	function void handle_clear_pdcm_data_buffer();
		if(pdcm_buffer.size() == 0) begin
			return;
		end
		if(tdma_scheme_upload_listener::schemes[channel].valid == 1'b0) begin
			// no TDMA scheme defined: just delete buffer
			pdcm_buffer.delete();
		end
		else begin
			int frames_to_be_deleted = pdcm_buffer.size();
			if(pdcm_buffer[$].frame_finished == 1'b0) begin
				// last frame is not finished yet so don't delete it
				frames_to_be_deleted--;
			end
			for (int i = 0; i < frames_to_be_deleted; i++) begin
				pdcm_buffer.pop_front;
			end
		end
		last_clear_pdcm_data_buffer_time = $time();
	endfunction
	
	// sync channels
	function void handle_sync_command_command(spi_sync_dsi_channels_seq sync_seq);
		// FIXME: implement more detailed handling of sync command
		if(sync_seq.channel_bits[channel] == 1'b1) begin
			external_sync_received = sync_seq.external_sync;
		end
	endfunction
	
	function void handle_read_crm_data_command(spi_read_crm_data_packets_seq read_seq);
		// special case for incomplete reads => don't clear buffer of second channel 
		if(channel == 1 && read_seq.channel_bits == 2'b11 && read_seq.incomplete == 1'b1 && read_seq.incomplete_word_count < 3) begin
			return;
		end
		if(read_seq.channel_bits[channel] == 1'b1) begin
			buffer_data_packet buffer_packet;
			spi_dsi_data_packet read_packet;
			
			buffer_packet = crm_buffer.pop_front();
			read_packet = read_seq.get_data_packet(channel, 1'b0);
			if(read_packet != null) begin				
				if(buffer_packet == null) begin
					// no data contained in buffer -> create an empty packet for comparison
					buffer_packet = create_empty_buffer_packet(2);
				end
				
				check_packet_header_flags(read_packet, buffer_packet);
				if(read_packet.symbol_count != 8'(buffer_packet.symbol_count)) begin
					`uvm_error(this.get_name(), $sformatf("unexpected symbol count in read CRM at channel %1b, expected %0d, read %0d symbols", channel, buffer_packet.symbol_count, read_packet.symbol_count))
				end
				
				foreach(read_packet.data[i]) begin
					if(buffer_packet.data[i] != read_packet.data[i]) begin
						`uvm_error(this.get_name(), $sformatf("read unexpected data in CRM at channel %1b at word %0d, expected 0x%4h, read 0x%4h", channel, i, buffer_packet.data[i], read_packet.data[i]))
					end
				end
			end
		end
	endfunction
	
	function void handle_read_pdcm_frame_command(spi_read_pdcm_frame_seq read_seq);
		// only channel one channel ("0") prints the read command (to avoid multiple outputs
		if(checker_config::get().enable_print_pdcm_read == 1'b1 && channel == 0) begin
			`uvm_info(get_type_name(), $sformatf("%s", read_seq.convert2string()), UVM_MEDIUM)
		end
		if(read_seq.channel_bits[channel] == 1'b1 && is_reading_enabled()) begin
			do_handle_read_pdcm_frame_command(read_seq);
		end
	endfunction

	function void do_handle_read_pdcm_frame_command(spi_read_pdcm_frame_seq read_seq);
		spi_pdcm_frame_header frame_header;
		pdcm_data_frame data_frame;
		
		// special case for incomplete reads => don't clear buffer of second channel
		if(channel == 1 && read_seq.channel_bits == 2'b11 && read_seq.incomplete == 1'b1) begin
			int first_channel_word_count = spi_read_pdcm_frame_seq::calculate_word_count(2'b01);
			if(read_seq.incomplete_word_count <= first_channel_word_count - 2) begin
				return;
			end
		end
		
		frame_header = read_seq.get_frame_header(channel, 1'b0);
		// gets next frame and removes it from buffer
		data_frame = get_next_pdcm_frame_from_buffer();
		
		// skip check if no frame header is set (this must be an incomplete read)
		if(frame_header == null) begin
			if(read_seq.incomplete == 1'b0) begin
				`uvm_error(this.get_name(), $sformatf("no frame header set in read PDCM sequence but read is not marked as incomplete"))
			end
			return;
		end
		// no valid TDMA scheme
		if(tdma_scheme_upload_listener::schemes[channel].valid == 1'b0) begin
			if(frame_header.packet_count != 8'd0) begin
				`uvm_error(this.get_name(), $sformatf("unexpected packet count in frame header for read without valid TDMA scheme at channel %1b, expected 0, got %0d packets", channel, frame_header.packet_count))
			end
		end
		else begin
			// no data has been received yet
			if(data_frame == null) begin
				spi_dsi_data_packet read_packets[$];
				if(frame_header.packet_count != 8'd0) begin
					`uvm_error(this.get_name(), $sformatf("unexpected packet count in frame header for read at channel %1b, expected 0, got %0d packets", channel, frame_header.packet_count))
				end
				// check that all read data is 0x0000
				read_seq.get_data_packets(channel, read_packets);
				foreach(read_packets[packet_index]) begin
					spi_dsi_data_packet next_packet = read_packets[packet_index];
					next_packet.check_values(0);
					if(next_packet.symbol_count != 8'd0) begin
						`uvm_error(this.get_name(), $sformatf("unexpected symbol count in packet %0d at channel %1b, expected 0, got %0d", packet_index, channel, next_packet.symbol_count))
					end
					foreach(next_packet.data[i]) begin
						logic[15:0] next_word = next_packet.data[i];
						if(next_word != 16'h0000) begin
							`uvm_error(this.get_name(), $sformatf("unexpected data in packet %0d at index %0d at channel %1b, expected 0x0000, got 0x%4h", packet_index, i, channel, next_word))
						end
					end
				end
			end
			else begin
				int expected_packet_count;
				spi_dsi_data_packet read_packets[$];
				read_seq.get_data_packets(channel, read_packets);
				
				// check frame header packet count
				expected_packet_count = data_frame.packet_count > 255 ? 255 : data_frame.packet_count;
				if(expected_packet_count != int'(frame_header.packet_count)) begin
					`uvm_error(this.get_name(), $sformatf("unexpected packet count in frame header for read at channel %1b, expected %0d, got %0d packets", channel, data_frame.packet_count, frame_header.packet_count))
				end
				// check frame header PC flag
				if(data_frame.get_value(PC) != frame_header.get_value(PC)) begin
					`uvm_error(this.get_name(), $sformatf("unexpected PC flag value in frame header for read at channel %1b, expected %1b, got %1b", channel, data_frame.get_value(PC), frame_header.get_value(PC)))
				end
				foreach(data_frame.packets[i]) begin
					if(i < read_packets.size()) begin
						buffer_data_packet buffer_packet = data_frame.packets[i];
						check_packet_header_flags(read_packets[i], buffer_packet, i);
						if(8'(buffer_packet.symbol_count) != read_packets[i].symbol_count) begin
							`uvm_error(this.get_name(), $sformatf("unexpected symbol count in packet %0d at channel %1b, expected %0d, got %0d", i, channel, buffer_packet.symbol_count, read_packets[i].symbol_count))
						end
						foreach(buffer_packet.data[k]) begin
							if(buffer_packet.data[k] != read_packets[i].data[k]) begin
								`uvm_error(this.get_name(), $sformatf("unexpected data in packet %0d at index %0d at channel %1b, expected 0x%4h, got 0x%4h", i, k, channel, buffer_packet.data[k], read_packets[i].data[k]))
							end
						end
					end
				end
				// read contains more data than expected
				if(read_packets.size() > data_frame.packets.size()) begin
					for (int i = data_frame.packets.size(); i < read_packets.size(); i++) begin
						foreach(read_packets[i].data[k]) begin
							if(read_packets[i].data[k] != 0) begin
								`uvm_error(this.get_name(), $sformatf("unexpected data in packet %0d at index %0d at channel %1b, expected 0x0000, got 0x%4h", i, k, channel, read_packets[i].data[k]))
							end
						end
					end
				end
			end
		end
	endfunction
	
	function pdcm_data_frame get_next_pdcm_frame_from_buffer();
		if(pdcm_buffer.size() == 0) begin
			return null;
		end
		// current frame has not been finished yet
		if(pdcm_buffer[0].frame_finished == 1'b0) begin
			return null;
		end
		return pdcm_buffer.pop_front();
	endfunction
	
	function void check_packet_header_flags(spi_dsi_data_packet read_packet, buffer_data_packet buffer_packet, int packet_index = -1);
		string packet_index_string = (packet_index < 0) ? "" : $sformatf("of packet index %0d ", packet_index);
		
		if(read_packet.get_value(SCE) != buffer_packet.get_value(SCE)) begin
			`uvm_error(this.get_name(), $sformatf("unexpected SCE (symbol count error) flag in packet header %sat channel %1b, expected %1b, read %1b", packet_index_string, channel, buffer_packet.get_value(SCE), read_packet.get_value(SCE)))
		end
		if(configuration_subscriber.crc_en == 1'b0) begin
			if(read_packet.get_value(CRC) != 1'b0) begin
				`uvm_error(this.get_name(), $sformatf("unexpected CRC flag for CRC_EN = 0 in packet header %sat channel %1b, expected 0, read %1b", packet_index_string, channel, read_packet.get_value(CRC)))
			end
		end 
		else begin
			if(read_packet.get_value(CRC) != buffer_packet.get_value(CRC)) begin
				`uvm_error(this.get_name(), $sformatf("unexpected CRC flag in packet header %sat channel %1b, expected %1b, read %1b", packet_index_string, channel, buffer_packet.get_value(CRC), read_packet.get_value(CRC)))
			end
		end
		if(buffer_packet.ignore_timing_error_flag == 1'b0) begin
			if(read_packet.get_value(TE) != buffer_packet.get_value(TE)) begin
				`uvm_error(this.get_name(), $sformatf("unexpected TE (timing error) flag in packet header %sat channel %1b, expected %1b, read %1b", packet_index_string, channel, buffer_packet.get_value(TE), read_packet.get_value(TE)))
			end
		end
		else begin
			`uvm_info(this.get_name(), $sformatf("ignored TE (timing error) flag %sbecause of gray zone timing", packet_index_string), UVM_MEDIUM)	
		end
		if(read_packet.get_value(SE) != buffer_packet.get_value(SE)) begin
			`uvm_error(this.get_name(), $sformatf("unexpected SE (symbol coding error) flag in packet header %sat channel %1b, expected %1b, read %1b", packet_index_string, channel, buffer_packet.get_value(SE), read_packet.get_value(SE)))
		end
		if(read_packet.get_value(VE) != buffer_packet.get_value(VE)) begin
			`uvm_error(this.get_name(), $sformatf("unexpected VE (voltage error) flag in packet header %sat channel %1b, expected %1b, read %1b", packet_index_string, channel, buffer_packet.get_value(VE), read_packet.get_value(VE)))
		end
		if(read_packet.get_value(CE) != buffer_packet.get_value(CE)) begin
			`uvm_error(this.get_name(), $sformatf("unexpected CE (CLKREF error) flag in packet header %sat channel %1b, expected %1b, read %1b", packet_index_string, channel, buffer_packet.get_value(CE), read_packet.get_value(CE)))
		end
	endfunction
	
	virtual function void compare_times(time time1, time time2, string message, time delta=0.0us);
		time diff = (time1 > time2) ? time1-time2 : time2-time1;
		if(diff > delta) begin
			`uvm_error(this.get_name(), $sformatf("%s differ by %0fus, expected maximum difference is %0fus.", message, diff/1.0us, delta/1.0us )) 
		end
	endfunction
endclass
