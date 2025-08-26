/**
 * Class: ecc_dsi3_transmit_data_error_seq
 * 
 * Sequence for generating ECC errors injected in DSI3 receiver data
 */
class ecc_dsi3_transmit_data_error_seq extends ecc_error_base_seq;
	
	`uvm_object_utils(ecc_dsi3_transmit_data_error_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_transmit_data_error");
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.DSI_CMD;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.DSI_CMD;
		path = $sformatf({PATH_DSI3_TRANSMIT_DATA}, channel);
		test = $sformatf("DSI3 transmit data ECC");
	endfunction
	
	virtual task apply_stimuli();
		spi_read_crm_data_packets_seq read;
		dsi3_crm_packet packets[$];
		spi_crm_seq crm_seq;
		
		create_valid_CRM_packets_with_data(packets);
		
		check_dab(1'b1);
		
		transaction_recorder.enable_recorder();
		transaction_recorder.clear_all();
		
		`spi_frame_begin
			`spi_frame_send(crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;
		check_dab(0);
		
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		check_dab(1'b1);
		
		check_master_transaction(crm_seq);
		check_data(read, packets);
		#100us;
		
	endtask
	
	//FIXME: move to dsi3_crm_packet (but there, dsi3_master_pkg is not available!!)
	virtual function dsi3_crm_packet create_packet_from_master_transaction(dsi3_master_tr master_transaction);
		dsi3_crm_packet packet = new();
		if (master_transaction.msg_type == dsi3_pkg::CRM ) begin
			convert_queue #(1, 4)::convert(master_transaction.data, packet.data);
			packet.check_crc();
			return packet;
		end
		else begin
			`uvm_error(this.get_type_name(), $sformatf("CRM packet could not be created from master transaction of type %s", master_transaction.msg_type))
			return null;
		end
	endfunction
	
	virtual function void check_master_transaction(spi_crm_seq crm_seq);
		crm_seq.crm_packet.crc_correct = 1'b1;
		crm_seq.crm_packet.update_crc();
		transaction_recorder.expect_tr_count_for_all_channels(1);
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			if ((selected_channel == channel) && (bit_error == TWO_BIT_ERR)) begin
				dsi3_crm_packet master_packet = create_packet_from_master_transaction(transaction_recorder.get_master_tr(selected_channel, 0));
				if (master_packet.crc_correct)
					`uvm_error(this.get_type_name(), $sformatf("CRC of master transaction is correct but expect incorrect CRC due to changes in output stream"))
			end
			else begin
				transaction_recorder.expect_packets(selected_channel, {crm_seq.crm_packet});
			end
		end
	endfunction
	
	virtual function void check_data(spi_read_crm_data_packets_seq read, dsi3_crm_packet packets[$]);
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			read.expect_flags( 2'(channel), packets[channel].crc_correct ? {} : {CRC});
			read.expect_packet(2'(channel), packets[channel]);
		end
	endfunction
	
	virtual task apply_error();
		virtual dsi3_slave_if vif = get_dsi3_master_config(channel).vif;
		fork
			begin
				@(negedge vif.cable.Voltage);
				#(50us);
				apply_ecc_failure();
				#1us;
				remove_ecc_failure();
			end
			begin
				#500us;
				`uvm_error(this.get_type_name(), $sformatf("DSI3 voltage did not go to LOW on channel %1d", channel))
			end
		join_any
		disable fork;
		#1us;
		if (bit_error == TWO_BIT_ERR)	check_HE_ic_status(1'b1);
		else 							check_HE_ic_status(1'b0);
	endtask
	
	
	virtual task apply_ecc_failure();
		random_data_error#(33)	data_error;
		uvm_hdl_data_t	data;
		
		if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
		else `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", path, data[32:0]), UVM_INFO)
		data_error = new(data[32:0], bit_error);
		if (!data_error.randomize()) begin
			`uvm_error(this.get_type_name(), "randomization of data_error failed")
		end
		`uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
		if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
	endtask
	
	virtual task remove_ecc_failure();
//		`uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
//		if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release %s failed!", path))
	endtask
		
	virtual task run_check_after_error();
		check_HE_ic_status(1'b0);
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
		check_HE_ic_status(1'b0);
	endtask
	
	virtual function int get_field_mask();
		int mask;
		mask = 1 << (irq_stat_ecc_field.get_lsb_pos()+channel);
		$display("mask=%4h", mask);
		return mask;
	endfunction
	
endclass

