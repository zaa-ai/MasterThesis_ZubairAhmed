class dsi3_sync_base_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_sync_base_seq)

	function new(string name = "dsi3_sync_base");
		super.new(name);
	endfunction
	
	virtual task run_tests();
		`uvm_error(get_type_name(), "this sequence must not be executed, it is only intended to be a base class for other sequences")
	endtask

	virtual task check_SYNC_ERR(int channel, bit expected);
		uvm_reg_data_t value;
		regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.SYNC_ERR.read(status, value);
		if(value != 64'(expected)) `uvm_error(this.get_name(), $sformatf("Read unexpected DSI_IRQ_STAT.SYNC_ERR value for channel %0d, expected %0b, got %0b.", channel, expected, value))
	endtask
	
	/**
	 * Clear all SYNC_ERR flags of all channels.
	 */
	virtual task clear_all_SYNC_ERR();
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			clear_SYNC_ERR(i);
		end
	endtask;
		
	/**
	 * Clear SYNC_ERR flag of given channel.
	 */	
	virtual task clear_SYNC_ERR(int channel);
		regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.SYNC_ERR.write(status, 1'b1);
	endtask

	virtual task expect_SYNC(int channel, logic[project_pkg::DSI_CHANNELS-1:0] sync_channels, bit pin);
		uvm_reg_data_t pin_value, channels_value, value;
				
		regmodel.DSI[channel].DSI3_channel_registers.SYNC.read(status, value);
		pin_value = regmodel.DSI[channel].DSI3_channel_registers.SYNC.PIN.get();
		channels_value = regmodel.DSI[channel].DSI3_channel_registers.SYNC.CHANNELS.get();
				
		if(pin_value != 64'(pin)) `uvm_error(this.get_type_name(), $sformatf("Unexpected SYNC.PIN value in register of channel %0d, expected %0d, got %0d", channel, pin, pin_value))
		if(channels_value != 64'(sync_channels)) `uvm_error(this.get_type_name(), $sformatf("Unexpected SYNC.CHANNELS value in register of channel %0d, expected 0b%02b, got 0b%02b", channel, sync_channels, channels_value))
	endtask	
		
	virtual task expect_SYNC_IDLE_REG(logic[project_pkg::DSI_CHANNELS-1:0] channels, bit syncb_pin);
		uvm_reg_data_t value, pin_value, channels_value;
			
		regmodel.DSI_common.common_DSI3_block_registers.SYNC_IDLE_REG.read(status, value);
		pin_value = regmodel.DSI_common.common_DSI3_block_registers.SYNC_IDLE_REG.PIN.get();
		channels_value = regmodel.DSI_common.common_DSI3_block_registers.SYNC_IDLE_REG.DSI.get();
					
		if(pin_value != 64'(syncb_pin)) `uvm_error(this.get_type_name(), $sformatf("Unexpected SYNC_IDLE_REG.PIN value, expected %0d, got %0d", syncb_pin, pin_value))
		if(channels_value != 64'(channels)) `uvm_error(this.get_type_name(), $sformatf("Unexpected SYNC_IDLE_REG.DSI value, expected 0b%02b, got 0b%02b", channels, channels_value))
	endtask	
	
	function void check_channel_sync(int channels, int sync_channels, time spi_end);
		time first_start = 0ns;
		for (int ch=0; ch < project_pkg::DSI_CHANNELS; ch++) begin
			time start_time = transaction_recorder.get_last_master_tr_begin_time(ch);
				
			if(start_time == 0) begin
				`uvm_error(this.get_name(), $sformatf("Expected a master transaction at channel %0d, but there seems to be none.", ch)) 
				return;
			end
				
			// channel is synced
			if(sync_channels[ch]) begin
								
				if(first_start == 0) first_start = start_time;
				else compare_times(first_start, start_time, "start times", 5ns);
	
				`uvm_info(get_type_name(), $sformatf("=> syncronized channels 0b%2b, start of channel %0d at %0fus", sync_channels, ch, start_time/1.0us), UVM_MEDIUM)
			end
			// channel is NOT synced
			else begin
				if(channels[ch] == 1'b0) begin
					// if there was only one CRM transmit it must be started directly after SPI frame finished
					compare_times(start_time, spi_end, "unsynced start time", 15us);
				end
			end
		end
	endfunction
	
	/**
	 * Adds one random command to given SPI frame.
	 */
	function void append_random_transmit_commands(spi_command_frame_seq frame, ref string commands);
		randcase
			3 : begin
				`spi_frame_create(spi_pdcm_seq, pulse_count inside {[1:5]};)
				commands = $sformatf("%s PDCM", commands);
			end
			3 : begin
				`spi_frame_create(spi_crm_seq, broad_cast == 1'b0;)
				commands = $sformatf("%s CRM", commands);
			end
			1 : begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, )
				commands = $sformatf("%s CLEAR_DSI_BUFFERS", commands);
			end
			2 : begin
				`spi_frame_create(spi_dsi_wait_seq, wait_time < 15'd500;)
				commands = $sformatf("%s WAIT", commands);
			end
		endcase
	endfunction
		
		
	function void check_pdcm_pulse_count(int pulse_count);
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			transaction_recorder.expect_tr_count(i, pulse_count);
		end
	endfunction
	
	function void check_pdcm_periods(time expected_period);
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			check_pdcm_period(i, expected_period);	
		end
	endfunction
	
	function void check_pdcm_period(int channel, time expected_period);
		for(int i=transaction_recorder.get_master_tr_count(channel)-1; i > 0; i--) begin
			time measured_period = transaction_recorder.get_master_tr_begin_time(channel, i) - transaction_recorder.get_master_tr_begin_time(channel, i-1);
			compare_times(expected_period, measured_period, $sformatf("expected PDCM period of channel %0d", channel), 1ns);
		end
	endfunction
	
	task expect_dsi_stat_sync_flag(logic[project_pkg::DSI_CHANNELS-1:0] channels);
		uvm_reg_data_t value;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.SYNC.read(status, value);
			if(value != 64'(channels[channel])) `uvm_error(this.get_name(), $sformatf("Unexpected DSI_STAT.SYNC flag for channel %0d, expected 0b%1b, got 0b%1b.", channel, channels[channel], 1'(value)))
		end
	endtask
		
	function void expect_tx_shift(logic[project_pkg::DSI_CHANNELS-1:0] channels, int tr_count, int tx_shift, time tolerance=7ns);
		time shift_time = tx_shift * 55.6ns;
			
		for (int tr_index=0; tr_index<tr_count; tr_index++) begin
			time expected_start = 0ns;
			int last_channel = 0;
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				if(channels[channel] == 1'b1) begin
					dsi3_master_tr tr = transaction_recorder.get_master_tr(channel, tr_index); 
					if(expected_start == 0ns) begin
						expected_start = tr.get_begin_time();
					end
					else begin
						compare_times(expected_start, tr.get_begin_time(), $sformatf("shift at transmission %0d between channel %0d and %0d", tr_index+1, last_channel, channel), tolerance);
					end
					last_channel = channel;
					expected_start = expected_start + shift_time;  
				end
			end
		end
	endfunction
	
	function int get_max_shift();
		return (2 ** regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.SHIFT.get_n_bits()) - 1;
	endfunction
	
	function int get_max_tx_shift(dsi3_pkg::dsi3_bit_time_e bit_time);
		return (dsi3_pkg::get_bit_time(bit_time) * 18) / 6;
	endfunction

	function int get_tx_shift_value(dsi3_pkg::dsi3_bit_time_e bit_time, int nrOfShiftSamples, int shiftIndex);
		int max_tx_shift = get_max_tx_shift(bit_time);
		return (max_tx_shift * shiftIndex) / nrOfShiftSamples;
	endfunction 
	
	task apply_tdma_scheme(tdma_scheme_pdcm scheme);
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			set_tdma_scheme_pdcm(i, scheme);
		end
		#50us;
	endtask
	
endclass
