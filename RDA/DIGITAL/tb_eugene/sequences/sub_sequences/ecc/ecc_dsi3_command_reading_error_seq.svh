/**
 * Class: ecc_dsi3_command_reading_jtag_ecc_inject_error_seq
 * 
 * Super sequence for applying ECC errors in DSI3 command blocks when reading DSI commands
 */
class ecc_dsi3_command_reading_jtag_ecc_inject_error_seq extends ecc_error_base_seq;
	
	rand int unsigned	bit_position;
	constraint c_bit {bit_position < project_pkg::ECC_WIDTH; }
	
	`uvm_object_utils(ecc_dsi3_command_reading_jtag_ecc_inject_error_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_command_reading_jtag_ecc_inject_error");
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.DSI_CMD;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.DSI_CMD;
		path = "is not relevant";
		test = $sformatf("DSI3 command reading ECC error on channel %1d", channel);
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
					`spi_frame_create(spi_dsi_wait_seq, wait_time==15'd500; channel_bits == 2'(1<<local::channel);)
					`spi_frame_create(spi_dsi_wait_seq, wait_time==15'd1000; channel_bits == ~(2'(1<<local::channel));)
					`spi_frame_create(spi_crm_seq, channel_bits=='1; broad_cast == 1'b0; )
                    `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			begin
				#1.5ms;
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
		#480us;
		apply_ecc_failure();
		#60us;
		remove_ecc_failure();
		
		if (bit_error == TWO_BIT_ERR)	check_HE_ic_status(1'b1);
		else 							check_HE_ic_status(1'b0);
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			if (selected_channel == channel) begin
				if ((selected_channel == channel) && (bit_error == TWO_BIT_ERR))
					registers.check_flag(regmodel.DSI[selected_channel].DSI3_channel_registers.DSI_CMD.CMD , 0);
				else
					registers.check_flag(regmodel.DSI[selected_channel].DSI3_channel_registers.DSI_CMD.CMD , CMD_CRM);
			end
			else
				registers.check_flag(regmodel.DSI[selected_channel].DSI3_channel_registers.DSI_CMD.CMD , CMD_DSI_WAIT);
		end
	endtask
	
	virtual task apply_ecc_failure();
		random_data_error#(6)	ecc_error;
		ecc_error = new(0, bit_error);
		if (!ecc_error.randomize()) begin
			`uvm_error(this.get_type_name(), "randomization of data_error failed")
		end
		
		jtag_enable(.initialize_jtag(1'b1));
		#5us;
		test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_ECC_CONTROL.ELIP_ECC.write(status, ecc_error.get_data());
		#5us;
		
	endtask
	
	virtual task remove_ecc_failure();
		jtag_disable();
	endtask
		
	virtual task run_check_after_error();
		check_HE_ic_status(1'b0);
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		check_HE_ic_status(1'b0);
	endtask

endclass
