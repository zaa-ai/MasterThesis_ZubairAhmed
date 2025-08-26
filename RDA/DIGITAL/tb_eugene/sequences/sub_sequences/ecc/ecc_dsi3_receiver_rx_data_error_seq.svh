/**
 * Class: ecc_dsi3_receiver_rx_data_error_seq
 * 
 * Sequence for generating ECC errors injected in DSI3 receiver data
 */
class ecc_dsi3_receiver_rx_data_error_seq extends ecc_error_base_seq;
	
	`uvm_object_utils(ecc_dsi3_receiver_rx_data_error_seq)
	
	protected	tdma_scheme schemes[project_pkg::DSI_CHANNELS-1:0];
    protected logic firstFrameAfterErrorValid = 1'b0;
	
	function new(string name = "");
		super.new("ecc_dsi3_receiver_rx_data_error_seq");
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_DATA;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_DATA;
		path = $sformatf({PATH_DSI3_RECEIVER_RX_DATA, ".ecc"}, channel);
		test = $sformatf("DSI3 rx data ECC");
    endfunction
    
	virtual task apply_stimuli();
        spi_read_pdcm_frame_seq read;
        tdma_scheme_pdcm scheme;
		transaction_recorder.enable_recorder();
		transaction_recorder.clear_all();
		
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            scheme = new();
            scheme.chiptime = 3;
            scheme.pdcm_period = 'd1000;
            scheme.valid = 1'b1;
            scheme.add_packet(tdma_scheme_packet_pdcm::new_packet(30, 70, 8, dsi3_pkg::SID_8Bit));
            schemes[selected_channel] = scheme;
            schemes[selected_channel].packets[0].packet = scheme.packets[0].packet;
            schemes[selected_channel].packets[0].earliest_start_time = scheme.packets[0].earliest_start_time;
            schemes[selected_channel].packets[0].latest_start_time = scheme.packets[0].latest_start_time;
            schemes[selected_channel].packets[0].tolerance_int = scheme.packets[0].tolerance_int;
            `upload_tdma_scheme_with(scheme, channels == 2'b11;)
            scheme.packets[0].earliest_start_time = scheme.packets[0].earliest_start_time + 5;
            scheme.packets[0].latest_start_time = scheme.packets[0].latest_start_time - 5;
            set_tdma_scheme_pdcm(selected_channel, scheme);
        end
        
        #10us;
		
		check_dab(1'b1);
		
        `spi_frame_begin
            `spi_frame_create(spi_pdcm_seq, channel_bits==2'b11; pulse_count == 8'd1;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #(scheme.pdcm_period * 1us);
        
		check_dab(1'b0);
		
        #2us;
		
        `spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
        check_dab(1'b1);
		
		// check results
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			transaction_recorder.expect_tr_count(selected_channel, 1);
			if ((selected_channel == this.channel) && (bit_error == TWO_BIT_ERR) && (firstFrameAfterErrorValid == 1'b0)) begin // only when double error occurs!
				read.expect_empty(2'(selected_channel), 0);
				clear_slave_crm_scheme_fifo(selected_channel);
			end
			else begin
				read.expect_flags( 2'(selected_channel), 0, schemes[selected_channel].packets[0].packet.crc_correct ? {} : {CRC});
				read.expect_packet_data(2'(selected_channel), 0, 0, schemes[selected_channel].packets[0].packet.get_word(0));
			end
		end
	endtask
	
	virtual task apply_error();
		virtual dsi3_slave_if vif = get_dsi3_master_config(channel).vif;
		fork
			begin
				@(negedge vif.cable.Voltage);
				#(150us+(3us*3*6));
			end
			begin
				#10ms;
				`uvm_error(this.get_type_name(), $sformatf("DSI3 voltage did not go to LOW on channel %1d", channel))
			end
		join_any
		disable fork;
		apply_ecc_failure();
		#1us;
		remove_ecc_failure();
		if (bit_error == TWO_BIT_ERR)	check_HE_ic_status(1'b1);
		else 							check_HE_ic_status(1'b0);
	endtask
	
	
	virtual task apply_ecc_failure();
		random_data_error#(6)	ecc_error;
		uvm_hdl_data_t	data;
		if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
		else `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", path, data[7:0]), UVM_INFO)
		ecc_error = new(data[5:0], bit_error);
		if (!ecc_error.randomize()) begin
			`uvm_error(this.get_type_name(), "randomization of data_error failed")
		end
		`uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, ecc_error.get_data()), UVM_INFO)
		if (! uvm_hdl_force(path, ecc_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
	endtask
	
	virtual task remove_ecc_failure();
		`uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
		if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release %s failed!", path))
	endtask
		
	virtual task run_check_after_error();
        `uvm_info(this.get_type_name(), $sformatf("CHECK AFTER ERROR STARTED"), UVM_INFO)
		check_HE_ic_status(1'b0);
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == channel;)
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		check_HE_ic_status(1'b0);
        `uvm_info(this.get_type_name(), $sformatf("CHECK AFTER ERROR FINISHED"), UVM_INFO)
	endtask
	
	virtual function int get_field_mask();
		int mask;
		mask = 1 << (irq_stat_ecc_field.get_lsb_pos());
		$display("mask=%4h", mask);
		return mask;
	endfunction
	
endclass

class ecc_dsi3_receiver_rx_data_error_while_idle_seq extends ecc_dsi3_receiver_rx_data_error_seq;

	`uvm_object_utils(ecc_dsi3_receiver_rx_data_error_while_idle_seq)
    
    //TODO: fix apply_stimuli check. Weil error im idle appliziert wird, wird das nächste pdcm cmd normal ausgeführt.
    //TODO: force vs. deposit: warum auch ecc_corr IRQ gesetzt?
	
	function new(string name = "");
		super.new("ecc_dsi3_receiver_rx_data_error_while_idle");
        set_name("ecc_dsi3_receiver_rx_data_error_while_idle");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		test = $sformatf("DSI3 rx data ECC when in IDLE");
//        firstFrameAfterErrorValid = 1'b1;
	endfunction
	
	virtual task apply_error();
		#75us;
		apply_ecc_failure();
		#1us;
		remove_ecc_failure();
        #5us;
		if (bit_error == TWO_BIT_ERR)	check_HE_ic_status(1'b1);
		else 							check_HE_ic_status(1'b0);
	endtask
	
endclass
