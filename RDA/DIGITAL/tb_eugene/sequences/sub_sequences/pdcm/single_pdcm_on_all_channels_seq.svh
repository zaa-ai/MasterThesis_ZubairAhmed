class single_pdcm_on_all_channels_seq extends base_dsi_master_seq;
    
    rand int unsigned bad_channel;
    rand bit all_channels_correct;
    rand bit invalidate_tdma_scheme;
    protected bit received_data;
    
    constraint co_channel {bad_channel < project_pkg::DSI_CHANNELS;}
    constraint co_invalidate_tdma_scheme {soft invalidate_tdma_scheme == 1'b0;}

	`uvm_object_utils(single_pdcm_on_all_channels_seq)
	
	function new(string name = "");
		super.new("single_pdcm_on_all_channels");
        received_data = 1'b1;
	endfunction : new
	
	virtual task run_tests();
        spi_read_pdcm_frame_seq read_seq;
        tdma_scheme_pdcm schemes[project_pkg::DSI_CHANNELS-1:0];
		log_sim_description("single PDCM on all channels", LOG_LEVEL_OTHERS);
		
		// some example from 521.42 simulation
		schemes[0] = tdma_scheme_pdcm_factory::single_packet_with_words({16'h65ff, 16'h84eb});
		schemes[1] = tdma_scheme_pdcm_factory::single_packet_with_words({16'h65ff, 16'h84eb});
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			schemes[channel].packets[0].id_symbol_count = dsi3_pkg::SID_8Bit;
			schemes[channel].pdcm_period = 300;
			
			`upload_tdma_scheme_with(schemes[channel], channels == 2'b01 << channel;)
            schemes[channel].packets[0].earliest_start_time = schemes[channel].packets[0].earliest_start_time + 5;
            schemes[channel].packets[0].latest_start_time = schemes[channel].packets[0].latest_start_time - 5;
			add_slave_pdcm_scheme(channel, schemes[channel]);
		end
		#50us;
        
        check_dab(1'b1);
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
        #1ms; 
        check_dab(~received_data);
        
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            if ((all_channels_correct == 1'b0) && (selected_channel == bad_channel) && (invalidate_tdma_scheme == 1'b1)) begin
                tdma_scheme_upload_listener::invalidate(selected_channel);
                clear_slave_pdcm_scheme_fifo(selected_channel);
            end
        end
        
        `spi_frame_begin
            `spi_frame_send(read_seq, channel_bits == 2'b11; )
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
 
        check_dab(1'b1);
        
        check_data(read_seq, schemes);
        
		#10us;
        
		read_and_check_empty_data();
		
        #100us;
    endtask
    
    virtual task check_data(spi_read_pdcm_frame_seq read_seq, tdma_scheme_pdcm schemes[project_pkg::DSI_CHANNELS-1:0]);
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            if ((all_channels_correct == 1'b0) && (selected_channel == bad_channel)) begin
                if(invalidate_tdma_scheme == 1'b0) begin
                    read_seq.expect_empty(2'(selected_channel), 0);
                end
                else begin
                    spi_read_status_seq status_seq; 
                    `spi_frame_begin
                    `spi_frame_send(status_seq, )
                    `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
                    `spi_frame_end_with_status(selected_channel == 0 ? {NT0} : {NT1})
                    status_seq.check_status_flags(selected_channel == 0 ? {NT0} : {NT1});
                end
            end
            else begin
                `uvm_info(this.get_type_name(), $sformatf("Check read for channel %0d", selected_channel), UVM_INFO)
                read_seq.expect_flags( 2'(selected_channel), 0, schemes[selected_channel].packets[0].packet.crc_correct ? {} : {CRC});
                read_seq.expect_packet(2'(selected_channel), 0, schemes[selected_channel].packets[0].packet);
            end
        end
    endtask
	
	task read_and_check_empty_data(logic[project_pkg::DSI_CHANNELS-1:0] channels = 2'b11);
		spi_read_pdcm_frame_seq empty_read_seq;
		
		`spi_frame_begin
		`spi_frame_send(empty_read_seq, channel_bits == channels;)
		`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            if ((all_channels_correct == 1'b0) && (selected_channel == bad_channel)) begin
                if(invalidate_tdma_scheme == 1'b0) begin
                    empty_read_seq.expect_empty(2'(selected_channel), 0);
                end
                else begin
                    spi_read_status_seq status_seq; 
                    `spi_frame_begin
                    `spi_frame_send(status_seq, )
                    `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
                    `spi_frame_end_with_status(selected_channel == 0 ? {NT0} : {NT1})
                    status_seq.check_status_flags(selected_channel == 0 ? {NT0} : {NT1});
                end
            end
            else begin
                `uvm_info(this.get_type_name(), $sformatf("Check read for channel %0d", selected_channel), UVM_INFO)
                empty_read_seq.expect_empty(2'(selected_channel), 0);
            end
        end
	endtask
endclass
