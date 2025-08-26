class crm_fill_buffer_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_fill_buffer_seq)
	
	function new(string name = "");
		super.new("crm_do_many_crms");
	endfunction
	
	virtual task run_tests();
		do_many_crms();
		fill_buffer_using_crms_without_answer();
	endtask
	
	task do_many_crms();
		int buffer_full_index = int'($floor(int'(project_pkg::SIZE_DSI_CRM_BUF - 16'd1) / 3)); // 3 words per CRM stored in buffer
		int buffer_warn_index = int'($floor(buffer_full_index * 0.75));
		
		log_sim_description("do many CRM TRANSMITs on all channels without reading data", LOG_LEVEL_SEQUENCE);
		
		for (int loop=0; loop<buffer_full_index + 10; loop++) begin
			spi_status_word_flags status_flags[$];
			
			`uvm_info(this.get_type_name(), $sformatf("CRM TRANSMIT number %0d", loop+1), UVM_MEDIUM)
			
			// expect data in buffers after first transmit
			status_flags = {NT0, NT1};
			if(loop > 0) begin
				status_flags.push_back(CR0);
				status_flags.push_back(CR1);
			end
			if(loop > buffer_warn_index) begin
				status_flags.push_back(BF);
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end_with_status(status_flags)
			#500us;
			
			check_buffer_states(loop, buffer_warn_index, buffer_full_index);
			// clear buffer full IRQ
			regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.write(status, 16'hFFFF);
		end
			
		// clear data from buffer
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
	endtask
	
	task fill_buffer_using_crms_without_answer();
		int buffer_full_index = int'(project_pkg::SIZE_DSI_CRM_BUF - 16'd1) - 1; // only status of CRM is stored in buffer (1 word); -1 because buffer can contain only 511 words
		int buffer_warn_index = int'($floor((project_pkg::SIZE_DSI_CRM_BUF - 16'd1) * 0.75));
		
		log_sim_description("do many CRMs without answer on all channels without reading data", LOG_LEVEL_SEQUENCE);
		
		for (int i=0; i<buffer_full_index + 10; i++) begin
			`uvm_info(this.get_type_name(), $sformatf("CRM TRANSMIT nummber %0d", i+1), UVM_MEDIUM)

			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;

			check_buffer_states(i, buffer_warn_index, buffer_full_index);
			// clear buffer full IRQ
			regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.write(status, 16'hFFFF);
		end
			
		// clear data from buffer
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
	endtask

	task check_buffer_states(int i, int buffer_warn_index, int buffer_full_index);
		if(i < buffer_warn_index) begin
			check_bfwb(1);
			check_buffer_fill_warning(2'b00);
			check_buffer_fill_error(2'b00);
		end
		// buffer fill warning
		else if(i >= buffer_warn_index && i < buffer_full_index) begin
			check_bfwb(0);
			check_buffer_fill_warning(2'b11);
			check_buffer_fill_error(2'b00);
		end
		// buffer fill error
		else if(i >= buffer_full_index) begin
			check_bfwb(0);
			check_buffer_fill_warning(2'b11);
			check_buffer_fill_error(2'b11);
			registers.check_flag(regmodel.SPI.SPI_registers.STATUS_WORD.BF, 1'b1);
		end
	endtask
	
	task check_buffer_fill_warning(logic[project_pkg::DSI_CHANNELS-1:0] warning_expected);
		uvm_reg_data_t value;
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_FILL_WARN.DSI_CRM_FW.read(status, value);
		if(value != 64'(warning_expected)) `uvm_error(this.get_name(), $sformatf("Unexpected BUF_FILL_WARN flags, expected 0b%02b, got 0b%02b.", warning_expected, value)) 
	endtask
	
	task check_buffer_fill_error(logic[project_pkg::DSI_CHANNELS-1:0] error_expected);
		uvm_reg_data_t value;
		regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.DSI_CRM_FE.read(status, value);
		if(value != 64'(error_expected)) `uvm_error(this.get_name(), $sformatf("Unexpected DSI data fill error flags, expected 0b%02b, got 0b%02b.", error_expected, value)) 
	endtask
endclass