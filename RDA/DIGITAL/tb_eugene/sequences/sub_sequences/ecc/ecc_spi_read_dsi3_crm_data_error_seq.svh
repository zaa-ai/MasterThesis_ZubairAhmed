/**
 * Class: ecc_spi_read_dsi3_crm_data_error_seq
 * 
 * sequence for applying ecc errors while reading from RAM
 */
class ecc_spi_read_dsi3_crm_data_error_seq extends ecc_error_base_seq;
	
	`uvm_object_utils(ecc_spi_read_dsi3_crm_data_error_seq)
	
	event	finished_preparation;
	event	applied_failure;
	event	finished_read;
	event	finished_read_data;
	rand	logic[15:0]	packet_data;
	
	function new(string name = "");
		super.new("ecc_spi_read_dsi3_crm_data_error_seq");
		
	endfunction
	
	virtual function void initialize();
		is_single_channel = 1'b1;
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_DATA;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_DATA;
		test = $sformatf("DSI3 data while reading DSI3 data with SPI of channel %1d", channel);
		path = $sformatf(PATH_RAM_DATA_READ_DATA);
	endfunction
	
	virtual task apply_stimuli();
		spi_read_crm_data_packets_seq read[project_pkg::DSI_CHANNELS-1:0];
		dsi3_crm_packet packets[$];
		transaction_recorder.enable_recorder();
		transaction_recorder.clear_all();
		
		create_valid_CRM_packets_with_data(packets);
		
		packet_data = packets[channel].get_word(1);
				
		check_dab(1'b1);
		
		fork
			begin
				`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits=='1; broad_cast == 1'b0; )
                `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			begin
				#0.5ms;
			end
		join
		check_dab(1'b0);
		for (int current_channel = 0; current_channel < project_pkg::DSI_CHANNELS; current_channel++) begin
			project_pkg::dsi_logic_t	channel_select;
			channel_select = project_pkg::dsi_logic_t'(1)<<current_channel;
			if (current_channel == channel) begin
				`uvm_create(read[current_channel]) //FIXME: create CASE for Euclide: if not present no error but fatal in simulation (null pointer access)
				if(read[current_channel].randomize() with {channel_bits == channel_select;} != 1) `uvm_error(this.get_name(), "randomization failed")
				send_separated_read_command(read[current_channel]);
			end
			else `spi_frame_begin
				`spi_frame_send(read[current_channel], channel_bits == channel_select;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end
		
		check_dab(1'b1);
		
		// modify packet data
		modify_packet_data(packets[channel]);
		
		// check results
		for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
			transaction_recorder.expect_tr_count(selected_channel, 1);
			if ((selected_channel == this.channel) && (bit_error == TWO_BIT_ERR)) begin // only when double error occurs!
				read[selected_channel].expect_flags( 2'(selected_channel), packets[selected_channel].crc_correct ? {} : {CRC});
				read[selected_channel].expect_packet(2'(selected_channel), packets[selected_channel]);
			end
			else begin
				read[selected_channel].expect_flags( 2'(selected_channel), packets[selected_channel].crc_correct ? {} : {CRC});
				read[selected_channel].expect_packet(2'(selected_channel), packets[selected_channel]);
			end
		end
		#10us;
		->finished_read_data;
	endtask
	
	virtual function void modify_packet_data(dsi3_crm_packet packet);
		if (bit_error==TWO_BIT_ERR) begin
			for (int nibble = 0; nibble < 4; nibble++) begin
				packet.data[7-nibble] = packet_data[(nibble+1)*4-1-:4];
			end
		end
	endfunction
	
	virtual task send_separated_read_command(ref spi_read_crm_data_packets_seq read);
		int spi_word;
		logic[15:0] temp_data_in[$];
		logic[15:0] temp_data_out[$];
        logic[15:0] crc_data_in[$];
        spi_tx_crc_request_seq tx_crc;
		spi_tr	spi_transaction;
		read.data_in.delete();
		read.data_out.delete();
		`uvm_do_on_with(spi_transaction, m_spi_agent.m_sequencer, {tr_type == SPI_START;})
		for (spi_word = 0; spi_word < read.get_word_count(); spi_word++) begin
            crc_data_in.push_back(read.get_word(spi_word));
			send_spi_transaction(read.get_word(spi_word), spi_word, spi_transaction);
			read.data_in.push_back(spi_transaction.data_in);
			read.data_out.push_back(spi_transaction.data_out);
			if (spi_word == 1) begin					
				-> finished_preparation;
				@applied_failure;
			end
			if (spi_word == 2) ->finished_read;
        end
        crc_data_in.push_back(16'h000);
		send_spi_transaction(16'h000, spi_word, spi_transaction);
		read.data_in.push_back(spi_transaction.data_in);
		read.data_out.push_back(spi_transaction.data_out);
		temp_data_in = read.data_in;
		temp_data_out = read.data_out;
		read.create_from(temp_data_in, temp_data_out);
        `uvm_create_on(tx_crc, m_spi_agent.m_sequencer)
        void'(tx_crc.randomize() with {mosi_crc_correct == 1'b1;});
        crc_data_in.push_back(tx_crc.get_word(0));
        tx_crc.mosi_crc = crc_calculation_pkg::spi_calculate_crc(1'b1, crc_data_in);
        `uvm_send(tx_crc)
		`uvm_do_on_with(spi_transaction, m_spi_agent.m_sequencer, {tr_type == SPI_END;})
	endtask
	
	virtual task send_spi_transaction(logic[15:0] word, int word_index, ref spi_tr spi_transaction);
		`uvm_create_on (spi_transaction, m_spi_agent.m_sequencer)
		spi_transaction.tr_type = spi_pkg::SPI_DATA;
		spi_transaction.data_in = word;
		spi_transaction.bit_count = 16;
		spi_transaction.word_index = word_index;
		spi_transaction.set_name("spi-data");
		`uvm_send (spi_transaction)		
	endtask
	
	virtual task apply_error();
		@(finished_preparation);
		#(5us);
		apply_ecc_failure();
		->applied_failure;
		@finished_read;
		remove_ecc_failure();
		@finished_read_data;
	endtask
	
	virtual task apply_ecc_failure();
		random_data_error#(16)	data_error;
		
		data_error = new(packet_data, bit_error);
		if (!data_error.randomize()) begin
			`uvm_error(this.get_type_name(), "randomization of data_error failed")
		end
		`uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
		if (! uvm_hdl_force(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
		packet_data = data_error.get_data();
	endtask
	
	virtual task remove_ecc_failure();
		if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
	endtask
	
	virtual task run_check_after_error();
		check_HE_ic_status(1'b0);
		if (bit_error == TWO_BIT_ERR) begin 
            `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel;)
            `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        end
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
	endtask
	
endclass
