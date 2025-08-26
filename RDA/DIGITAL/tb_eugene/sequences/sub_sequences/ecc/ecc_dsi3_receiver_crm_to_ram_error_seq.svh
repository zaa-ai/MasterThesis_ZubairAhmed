/**
 * Class: ecc_dsi3_receiver_crm_to_ram_error_seq
 * 
 * Sequence for generating ECC errors injected in DSI3 receiver while storing data in RAM
 */
class ecc_dsi3_receiver_crm_to_ram_error_seq extends ecc_error_base_seq;
	
	`uvm_object_utils(ecc_dsi3_receiver_crm_to_ram_error_seq)
	
    dsi3_crm_packet packets[$];
	
	function new(string name = "");
		super.new("ecc_dsi3_receiver_crm_to_ram_error");
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.RAM;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.RAM;
		path = $sformatf({PATH_DSI3_RECEIVER_CRM_TO_RAM, ".data.ecc"}, channel);
		test = $sformatf("DSI3 data writing ECC");
	endfunction
	
	virtual task apply_stimuli();
        transaction_recorder.enable_recorder();
        transaction_recorder.clear_all();
        
        create_valid_CRM_packets_with_data(packets);
        
        check_dab(1'b1);
        
        fork
            begin
                `spi_frame_begin
                    `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0; )
                    `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                `spi_frame_end
            end
            begin
                #1.5ms;
            end
        join
        
		check_data();

	endtask
	
	virtual task check_data();
        spi_read_crm_data_packets_seq read;
		if ((bit_error == TWO_BIT_ERR)) check_dab(1'b1); // everything is cleared!
		else 							check_dab(1'b0);
		
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
				read.expect_empty(2'(selected_channel));
				clear_slave_crm_scheme_fifo(selected_channel);
			end
			else begin
				read.expect_flags( 2'(selected_channel), packets[selected_channel].crc_correct ? {} : {CRC});
                read.expect_packet(2'(selected_channel), packets[selected_channel]);
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
        #20us;
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
		convert_queue #(4, 16)::convert(packets[channel].data, data_queue);
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
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send(single_pdcm_on_all_channels_fail_seq)
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
