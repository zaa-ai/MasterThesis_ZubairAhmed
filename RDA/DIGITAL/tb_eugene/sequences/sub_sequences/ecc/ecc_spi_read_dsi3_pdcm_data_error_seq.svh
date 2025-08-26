/**
 * Class: ecc_spi_read_dsi3_pdcm_data_error_seq
 * 
 * sequence for applying ecc errors while reading from RAM
 */
class ecc_spi_read_dsi3_pdcm_data_error_seq extends ecc_error_base_seq;
	
	`uvm_object_utils(ecc_spi_read_dsi3_pdcm_data_error_seq)
	
	event	finished_preparation;
	event	applied_failure;
	event	finished_read;
	event	finished_read_data;
	rand	logic[15:0]	packet_data;
    int word_index;
	
	function new(string name = "");
		super.new("ecc_spi_read_dsi3_pdcm_data_error_seq");
		
	endfunction
	
	virtual function void initialize();
		is_single_channel = 1'b1;
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_DATA;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_DATA;
		test = $sformatf("DSI3 data while reading DSI3 data with SPI of channel %1d", channel);
		path = $sformatf(PATH_RAM_DATA_READ_DATA);
        word_index = 1;
	endfunction
	
	virtual task apply_stimuli();
        spi_read_pdcm_frame_seq read[project_pkg::DSI_CHANNELS-1:0];
        tdma_scheme_packet    packets[$];
        tdma_scheme_pdcm schemes[project_pkg::DSI_CHANNELS-1:0];
        spi_pdcm_seq    pdcm_seq;
        tdma_scheme_pdcm scheme;
        bit all_channels_correct = (bit_error != TWO_BIT_ERR) ? 1'b1 : 1'b0;
        
		transaction_recorder.enable_recorder();
		transaction_recorder.clear_all();
        
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            dsi3_pdcm_packet    packet;
            
            packet = create_random_packet(.symbol_count(12), .sid(dsi3_pkg::SID_0Bit));
            scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet);
            scheme.pdcm_period = 'd500;
            scheme.packets[0].packet.check_crc();
            scheme.set_source_id_for_all_packets(dsi3_pkg::SID_0Bit);
            schemes[selected_channel] = scheme;
            schemes[selected_channel].packets[0].packet = scheme.packets[0].packet;
            schemes[selected_channel].packets[0].earliest_start_time = scheme.packets[0].earliest_start_time;
            schemes[selected_channel].packets[0].latest_start_time = scheme.packets[0].latest_start_time;
            schemes[selected_channel].packets[0].tolerance_int_min = 1000;
            schemes[selected_channel].packets[0].tolerance_int = 1000;
            schemes[selected_channel].packets[0].tolerance_int_max = 1000;
            `upload_tdma_scheme_with(scheme, channels == (2'b1 << selected_channel);)
            scheme.packets[0].earliest_start_time = scheme.packets[0].earliest_start_time + 5;
            scheme.packets[0].latest_start_time = scheme.packets[0].latest_start_time - 5;
            add_slave_pdcm_scheme(selected_channel, scheme);
            packets[selected_channel] = scheme.packets[0];
        end
		
		packet_data = packets[channel].packet.get_word(word_index);
				
		check_dab(1'b1);
		
		fork
			begin
				`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits=='1; pulse_count == 8'd1; )
                `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			begin
				#0.5ms;
			end
        join
        
        #200us;
        
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
				read[selected_channel].expect_flags( 2'(selected_channel), 0, packets[selected_channel].packet.crc_correct ? {} : {CRC});
				read[selected_channel].expect_packet(2'(selected_channel), 0, packets[selected_channel].packet);
			end
			else begin
				read[selected_channel].expect_flags( 2'(selected_channel), 0, packets[selected_channel].packet.crc_correct ? {} : {CRC});
				read[selected_channel].expect_packet(2'(selected_channel), 0, packets[selected_channel].packet);
			end
		end
		#10us;
		->finished_read_data;
	endtask
	
	virtual function void modify_packet_data(tdma_scheme_packet packet);
        logic[15:0] words[$];
        if (bit_error==TWO_BIT_ERR) begin
            packet.packet.get_data_in_words(words);
            foreach(words[i]) begin
                if(i < word_index) begin
                    // do nothing
                end
                else if(i == word_index)begin
                    // alter first word in packet
                    words[i] = packet_data;                  
                end
                else begin
                    // clear other words due to HW clearing
                    words[i] = '0;
                end
            end
            packet.packet.set_data(words);
        end
	endfunction
	
	virtual task send_separated_read_command(ref spi_read_pdcm_frame_seq read);
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
			if (spi_word == 2) begin					
				-> finished_preparation;
				@applied_failure;
			end
			if (spi_word == 3) ->finished_read;
        end
        crc_data_in.push_back(16'h000);
		send_spi_transaction(16'h000, spi_word, spi_transaction);
		read.data_in.push_back(spi_transaction.data_in);
		read.data_out.push_back(spi_transaction.data_out);
		temp_data_in = read.data_in;
		temp_data_out = read.data_out;
		read.create_from(temp_data_in, temp_data_out);
        #1us;
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
        `uvm_info(this.get_type_name(), $sformatf("packet_data = %2h", packet_data ), UVM_INFO)
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
