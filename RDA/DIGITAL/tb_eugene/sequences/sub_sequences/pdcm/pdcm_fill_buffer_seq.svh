class pdcm_fill_buffer_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_fill_buffer_seq)

	function new(string name = "");
		super.new("pdcm_fill_buffer");
	endfunction
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		int buffer_full_index = int'($floor((project_pkg::SIZE_DSI_PDCM_BUF - 16'd1) / 16'd4)); // 1 frame header + 1 packet header + 2 data words per period stored in buffer
		int buffer_warn_index = int'($floor(buffer_full_index * 0.75));
		
		log_sim_description("do many PDCMs on all channels without reading data", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = 200;
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us;
		
		// do PDCM
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int i=0; i<260; i++) begin
			spi_read_status_seq status_seq;	
			spi_status_word_flags status_flags[$];
			
			// wait for PDCM pulse
			wait_for_voltage_edge_at_channel(0, 1ms);
			`uvm_info(this.get_type_name(), $sformatf("PDCM period number %0d", i+1), UVM_MEDIUM)
				
			// expect data in buffers after first transmit
			if(i > 0) begin
				status_flags = {PD1, PD0};
			end
			// check SPI status word
			if(i > buffer_warn_index) begin
				status_flags.push_back(BF);
			end
			
			// check IC status
			`spi_frame_begin
				`spi_frame_send(status_seq,)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			status_seq.check_status_flags(status_flags);

			if(i <= buffer_warn_index) begin
				check_bfwb(1);
				check_buffer_fill_warning(2'b00);
				check_buffer_fill_error(2'b00);
			end
			// buffer fill warning
			else if(i >= buffer_warn_index && i <= buffer_full_index) begin
				check_bfwb(0);
				check_buffer_fill_warning(2'b11);
				check_buffer_fill_error(2'b00);
			end
			// buffer fill error
			else if(i > buffer_full_index) begin
				check_bfwb(0);
				check_buffer_fill_warning(2'b11);
				check_buffer_fill_error(2'b11);
			end
			// clear buffer full IRQ
			regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.write(status, 16'hFFFF);
		end
		#(scheme.pdcm_period / 2 * 1us);
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;
		
		//  read and check data	
		for(int i = 0; i < buffer_full_index; i++) begin	
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
		end
		// there must be no more data left
		repeat(5) begin
			spi_read_pdcm_frame_seq read_seq;
	
			`spi_frame_begin
				`spi_frame_send(read_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			read_seq.expect_packet_count(2'd0, 8'd0);
			read_seq.expect_empty(2'd0, 0);
			read_seq.expect_packet_count(2'd1, 8'd0);
			read_seq.expect_empty(2'd1, 0);
		end
	endtask
	
	task check_buffer_fill_warning(logic[project_pkg::DSI_CHANNELS-1:0] warning_expected);
		uvm_reg_data_t value;
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_FILL_WARN.DSI_PDCM_FW.read(status, value);
		if(value != 64'(warning_expected)) begin
			`uvm_error(this.get_name(), $sformatf("Unexpected BUF_FILL_WARN flags, expected %02b, got %02b.", warning_expected, value))
			log_sim_check("BUF_FILL_WARN", .status("FAIL"));
		end
		else begin
			log_sim_check("BUF_FILL_WARN", .status("PASS"));
		end
	endtask
	
	task check_buffer_fill_error(logic[project_pkg::DSI_CHANNELS-1:0] error_expected);
		uvm_reg_data_t value;
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.DSI_PDCM_FE.read(status, value);
		if(value != 64'(error_expected)) begin
			`uvm_error(this.get_name(), $sformatf("Unexpected DSI data fill error flags, expected %02b, got %02b.", error_expected, value))
			log_sim_check("BUF_IRQ_STAT", .status("PASS"));
		end
		else begin
			log_sim_check("BUF_IRQ_STAT", .status("PASS"));
		end
	endtask
endclass
