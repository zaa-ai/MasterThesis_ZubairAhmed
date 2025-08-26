/**
 * Class: ecc_dsi3_command_buffer_error_seq
 * 
 * Super sequence for applying ecc errors in DSI3 command blocks
 */
class ecc_dsi3_command_buffer_error_seq #(int bit_width=8) extends ecc_error_base_seq;
	
	`uvm_object_param_utils(ecc_dsi3_command_buffer_error_seq #(bit_width))
	
	function new(string name = "");
		super.new(name);
	endfunction
	
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.DSI_CMD_BUF;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.DSI_CMD_BUF;
	endfunction
	
	virtual task apply_stimuli();
		spi_read_crm_data_packets_seq read;
		dsi3_crm_packet packets[$];
		transaction_recorder.enable_recorder();
		transaction_recorder.clear_all();
		
		create_valid_CRM_packets_with_data(packets);
		
		check_dab(1'b1);
		
		fork
			begin
				`spi_frame_begin
					`spi_frame_create(spi_dsi_wait_seq, wait_time==15'd500; channel_bits == '1;)
					`spi_frame_create(spi_crm_seq, channel_bits=='1; broad_cast == 1'b0; )
                    `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			begin
				#1ms;
			end
		join
		check_dab(1'b0);
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		check_dab(1'b1);
		
		// check results
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			if ((selected_channel == this.channel) && (bit_error == TWO_BIT_ERR)) begin // only when double error occurs!
				transaction_recorder.expect_tr_count(selected_channel, 0);
				read.expect_empty(2'(selected_channel));
				clear_slave_crm_scheme_fifo(selected_channel);
			end
			else begin
				transaction_recorder.expect_tr_count(selected_channel, 1);
				read.expect_flags( 2'(selected_channel), packets[selected_channel].crc_correct ? {} : {CRC});
				read.expect_packet(2'(selected_channel), packets[selected_channel]);
			end
		end
	endtask
	
	virtual task apply_error();
		#350us;
		apply_ecc_failure();
		#20us;
		if (bit_error == TWO_BIT_ERR)	check_HE_ic_status(1'b1);
		else 							check_HE_ic_status(1'b0);
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			if ((selected_channel == channel) && (bit_error == TWO_BIT_ERR))
				registers.check_flag(regmodel.DSI[selected_channel].DSI3_channel_registers.DSI_CMD.CMD , 0);
			else
				registers.check_flag(regmodel.DSI[selected_channel].DSI3_channel_registers.DSI_CMD.CMD , CMD_DSI_WAIT);
		end
	endtask
	
	virtual task apply_ecc_failure();
		random_data_error#(bit_width)	data_error;
		uvm_hdl_data_t			data_read;
		
		if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
		`uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
		data_error = new(data_read[bit_width-1:0], bit_error);
		if (!data_error.randomize()) begin
			`uvm_error(this.get_type_name(), "randomization of data_error failed")
		end
		
		`uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
		if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
	endtask
	
	virtual task run_check_after_error();
		check_HE_ic_status(1'b0);
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		check_HE_ic_status(1'b0);
	endtask

endclass

/**
 * Class: ecc_dsi3_command_buffer_fsm_seq
 * 
 * sequence for applying ECC errors in DSI3 command buffer fsm
 */
class ecc_dsi3_command_buffer_fsm_seq extends ecc_dsi3_command_buffer_error_seq#(8);
	
	`uvm_object_utils(ecc_dsi3_command_buffer_fsm_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_command_buffer_fsm_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_COMMAND_BUFFER_FSM_STATE, channel);
		test = "DSI3 command buffer FSM state";
	endfunction
	
endclass


/**
 * Class: ecc_dsi3_command_buffer_read_pointer_seq
 * 
 * sequence for applying ECC errors in DSI3 command buffer read pointer
 */
class ecc_dsi3_command_buffer_read_pointer_seq extends ecc_dsi3_command_buffer_error_seq#(7);

	`uvm_object_utils(ecc_dsi3_command_buffer_read_pointer_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_command_buffer_read_pointer_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_COMMAND_BUFFER_READ_POINTER, channel);
		test = "DSI3 command buffer read pointer";
	endfunction
	
endclass

/**
 * Class: ecc_dsi3_command_buffer_write_pointer_seq
 * 
 * sequence for applying ECC errors in DSI3 command buffer write pointer
 */
class ecc_dsi3_command_buffer_write_pointer_seq extends ecc_dsi3_command_buffer_error_seq#(7);

	`uvm_object_utils(ecc_dsi3_command_buffer_write_pointer_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_command_buffer_write_pointer_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_COMMAND_BUFFER_WRITE_POINTER, channel);
		test = "DSI3 command buffer write pointer";
	endfunction
	
	virtual task run_check_after_error();
		check_HE_ic_status(1'b0);
		if (bit_error == TWO_BIT_ERR) begin
			`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel;) 
		end
		else begin
			`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        end
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		check_HE_ic_status(1'b0);
	endtask
	
endclass

/**
 * Class: ecc_dsi3_command_buffer_valid_pointer_seq
 * 
 * sequence for applying ECC errors in DSI3 command buffer valid pointer
 */
class ecc_dsi3_command_buffer_valid_pointer_seq extends ecc_dsi3_command_buffer_error_seq#(7);

	`uvm_object_utils(ecc_dsi3_command_buffer_valid_pointer_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_command_buffer_valid_pointer_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_COMMAND_BUFFER_VALID_POINTER, channel);
		test = "DSI3 command buffer valid pointer";
	endfunction
	
	virtual task run_check_after_error();
		check_HE_ic_status(1'b0);
		if (bit_error == TWO_BIT_ERR) begin
			`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel;) 
		end
		else begin
			`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        end
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		check_HE_ic_status(1'b0);
	endtask
	
endclass
