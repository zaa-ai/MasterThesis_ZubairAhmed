class random_pdcm_seq extends base_dsi_master_seq;
	
	rand int symbol_count;
	rand logic[7:0] pulse_count;
	rand logic[project_pkg::DSI_CHANNELS-1:0] channels;
	rand dsi3_pkg::sid_length_e source_id;
	rand int chip_time;
	
	bit enable_dab_check = 1'b1;
	
	constraint co_channels  {channels > 2'b00;}
	constraint co_chip_time {chip_time inside {[2:5]};}
	
	`uvm_object_utils_begin (random_pdcm_seq)
		`uvm_field_int  (symbol_count, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int  (pulse_count, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int  (channels, UVM_DEFAULT | UVM_BIN )
	`uvm_object_utils_end
	
	function new(string name = "");
		super.new("random_pdcm");
	endfunction
	
	task run_tests();
		fork
			watch_dab();
			do_pdcm();
		join_any
		disable fork;
	endtask
	
	task watch_dab();
		forever begin
			@(posedge dab.D);
			if(enable_dab_check == 1'b1) begin
				`uvm_error(this.get_type_name(), $sformatf("Got unexpected posedge at DAB pin"))
			end
		end
	endtask
	
	task do_pdcm();
		tdma_scheme_pdcm scheme = new();
		spi_pdcm_seq pdcm_seq;
		spi_read_pdcm_frame_seq read_seq;

		log_sim_description($sformatf("%0d periods of random packets with %0d symbols and SID 0b%02b at %0dus chip time on channels 0b%02b", pulse_count, symbol_count, source_id, chip_time, channels), LOG_LEVEL_SEQUENCE);
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CHIPTIME.write(status, uvm_reg_data_t'(chip_time - 2));
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == local::symbol_count; symbol_count_max == local::symbol_count; chiptime == local::chip_time; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		`upload_tdma_scheme_with(scheme, channels == local::channels;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us;
		
		`spi_frame_begin
			`spi_frame_send(pdcm_seq, channel_bits == channels; pulse_count == local::pulse_count;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
		
		for(int period_index = int'(pulse_count); period_index > 0; period_index--) begin
			#(scheme.pdcm_period * 1us);
			enable_dab_check = 1'b0;	
			`spi_frame_begin
				`spi_frame_send(read_seq, channel_bits == local::channels;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			enable_dab_check = 1'b1;
		end
		#(scheme.pdcm_period * 1us);
		#100us;
		
		// clear data buffers
		enable_dab_check = 1'b0;	
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == channels; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#10us;
		enable_dab_check = 1'b1;	
		check_dab(1'b1);		
		check_for_hardware_error();
	endtask
	
	task check_for_hardware_error();
		spi_read_status_seq status_seq;	
		`spi_frame_begin
			`spi_frame_send(status_seq,)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		if(status_seq.status.get_value(HE) == 1'b1) begin
			`uvm_error(this.get_name(), $sformatf("Got unexpected HE (hardware error) flag in status word"))
			// clear all DSI channel IRQs
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.write(status, 16'hFFFF);
			end			
		end
	endtask
endclass
