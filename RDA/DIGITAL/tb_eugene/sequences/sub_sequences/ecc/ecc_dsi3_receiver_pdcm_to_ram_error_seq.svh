/**
 * Class: ecc_dsi3_receiver_pdcm_to_ram_error_seq
 * 
 * Sequence for generating ECC errors injected in DSI3 receiver while storing data in RAM
 */
class ecc_dsi3_receiver_pdcm_to_ram_error_seq extends ecc_error_base_seq;
	
	`uvm_object_utils(ecc_dsi3_receiver_pdcm_to_ram_error_seq)
	
	protected	tdma_scheme schemes[project_pkg::DSI_CHANNELS-1:0];
	
	function new(string name = "");
		super.new("ecc_dsi3_receiver_pdcm_to_ram_error_seq");
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.RAM;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.RAM;
		path = $sformatf({PATH_DSI3_RECEIVER_PDCM_TO_RAM, ".data.ecc"}, channel);
		test = $sformatf("DSI3 data writing ECC");
	endfunction
	
	virtual task apply_stimuli();
        tdma_scheme_pdcm scheme;
        transaction_recorder.enable_recorder();
        transaction_recorder.clear_all();
        
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            scheme = new();
            scheme.chiptime = 3;
            scheme.pdcm_period = 'd400;
            scheme.valid = 1'b1;
            scheme.add_packet(tdma_scheme_packet_pdcm::new_packet(30, 70, 8, dsi3_pkg::SID_8Bit));
            schemes[selected_channel] = scheme;
            schemes[selected_channel].packets[0].packet = scheme.packets[0].packet;
            schemes[selected_channel].packets[0].earliest_start_time = scheme.packets[0].earliest_start_time;
            schemes[selected_channel].packets[0].latest_start_time = scheme.packets[0].latest_start_time;
            schemes[selected_channel].packets[0].tolerance_int = scheme.packets[0].tolerance_int;
            set_tdma_scheme_pdcm(selected_channel, scheme);
        end
        
        `upload_tdma_scheme_with(scheme, channels == 2'b11;)
        
        #10us;
        
        check_dab(1'b1);
        
        `spi_frame_begin
            `spi_frame_create(spi_pdcm_seq, channel_bits==2'b11; pulse_count == 8'd1;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #(scheme.pdcm_period * 1us);
        
		check_data();
	endtask
	
	virtual task check_data();
        spi_read_pdcm_frame_seq read;
		if ((bit_error == TWO_BIT_ERR)) begin
            check_dab(1'b1); // everything is cleared!
            for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
                tdma_scheme_upload_listener::invalidate(selected_channel);
                clear_slave_pdcm_scheme_fifo(selected_channel);
            end
        end
		else begin
            check_dab(1'b0);
        end
		
        #10us;
        
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
        
		check_dab(1'b1);
		
		// check results
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			transaction_recorder.expect_tr_count(selected_channel, 1);
			if ((bit_error == TWO_BIT_ERR)) begin // only when double error occurs!
                spi_read_status_seq status_seq; 
                `spi_frame_begin
                `spi_frame_send(status_seq, )
                `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
                `spi_frame_end_with_status({NT0, NT1})
                status_seq.check_status_flags({NT0, NT1});
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
                @(vif.cable.Current);
                #(3us * 3 * 6);
				//#(5us + schemes[channel].packets[0].get_start_time() + (3us*3*6) );
			end
			begin
				#500us;
				`uvm_error(this.get_type_name(), $sformatf("DSI3 voltage did not go to LOW on channel %1d", channel))
			end
		join_any
		disable fork;
		apply_ecc_failure();
		#25us;
		remove_ecc_failure();
		if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
        end
		else begin
            check_HE_ic_status(1'b0);
        end
	endtask
	
	virtual task apply_ecc_failure();
		random_data_error#(6)	ecc_error;
		logic[15:0]	data_queue[$];
		convert_queue #(4, 16)::convert(schemes[channel].packets[0].packet.data, data_queue);
		ecc_error = new(ECC_pkg::DWF_ecc_gen_chkbits(16, 6, data_queue[1]), bit_error);
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
		check_HE_ic_status(1'b0);
        if (bit_error == TWO_BIT_ERR) `create_and_send(single_crm_on_all_channels_all_fail_seq)
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		check_HE_ic_status(1'b0);
	endtask
	
	virtual function int get_field_mask();
		int mask;
		mask = 1 << (irq_stat_ecc_field.get_lsb_pos());
		$display("mask=%4h", mask);
		return mask;
	endfunction

endclass
