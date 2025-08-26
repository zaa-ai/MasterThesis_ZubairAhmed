class dsi_pdcm_data_buffer_status_seq extends base_dsi_master_seq;
    
    rand int	pdcm_frames;
    rand logic[project_pkg::DSI_CHANNELS-1:0] channels;
    rand int	symbol_count;
    rand int 	packet_count;
    
    constraint co_commands	{pdcm_frames inside {[1:10]};}
    constraint co_channels	{channels > 0; $countones(channels) > 1;}
    constraint co_symbols	{symbol_count inside {[8:30]};}
    constraint co_packets   {packet_count inside {[1:15]};}
    
    dsi_pdcm_data_buffer_status	buffer_status[project_pkg::DSI_CHANNELS-1:0];
    
    protected   tdma_scheme_pdcm schemes[project_pkg::DSI_CHANNELS-1:0];
    
    `uvm_object_utils(dsi_pdcm_data_buffer_status_seq) 
    
    function new(string name = "");
        super.new("dsi_data_buffer_status_seq");
    endfunction : new
    
    virtual task run_tests();
        tdma_scheme_pdcm scheme;
        channels = 2'b11;
        //        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
        //            scheme = new();
        //            void'(scheme.randomize() with {symbol_count_min == symbol_count;symbol_count_max == symbol_count; packets.size == packet_count;});
        //            foreach(scheme.packets[i]) begin
        //                dsi3_pdcm_packet packet = dsi3_pdcm_packet'(scheme.packets[i].packet); 
        //                packets.push_back(packet);
        //            end
        //            schemes[channel] = scheme;
        //            `uvm_info(this.get_type_name(), $sformatf("overall max pdcm period = %0d", calculateMaxPdcmPeriod()), UVM_INFO);
        //            scheme.pdcm_period = 10000;
        //            schemes[channel] = scheme;
        //            set_tdma_scheme_pdcm(channel, scheme);
        //            `upload_tdma_scheme_with(scheme, channels == (2'b1 << channel);)
        //        end
        scheme = new();
        void'(scheme.randomize() with {symbol_count_min == symbol_count;symbol_count_max == symbol_count; packets.size == packet_count; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;});
        //        scheme.pdcm_period = scheme.pdcm_period + 200;
        schemes[0] = scheme;
        schemes[1] = scheme;
        set_tdma_scheme_pdcm(0, scheme);
        set_tdma_scheme_pdcm(1, scheme);
        `upload_tdma_scheme_with(scheme, channels == 2'b11;)
        
        #100us;
        
        transaction_recorder.enable_recorder();
        
        check_dab(1'b1);
        
        create_and_initialize_buffer_status_classes(buffer_status);
        
        log_sim_description($sformatf("start PDCM with %1d frames containing %1d packets with %1d symbols on channels %0b", pdcm_frames, packet_count, symbol_count, channels), 2);
        
        `spi_frame_begin
        `spi_frame_create(spi_pdcm_seq, channel_bits == local::channels; pulse_count == local::pdcm_frames[7:0];)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        check_registers_at_each_pulse();
        
        #100us;
        
        read_data_packets();
        
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channels[channel]==1'b1)
                transaction_recorder.expect_tr_count(channel, pdcm_frames);
            else
                transaction_recorder.expect_tr_count(channel, 0);
        end
        
        check_dab(1'b1);
        #100us;
        
    endtask
    
    virtual function int calculateMaxPdcmPeriod();
        int period[$];
        int periods[project_pkg::DSI_CHANNELS-1:0];
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            tdma_scheme_packet packets[$] = schemes[channel].packets;
            tdma_scheme_packet last_packet = packets[schemes[channel].get_packet_count()-1];
            periods[channel] = last_packet.calculate_endtime_of_packet(schemes[channel].chiptime);
        end
        period = periods.max();
        return (period.size != 0) ? period[0] : 0;
    endfunction
    
    virtual task check_registers_at_each_pulse();
        wait_for_PDCM_pulse();
        buffer_status[0].write(1); // Frame header
        buffer_status[0].compare_buffer_registers();
        buffer_status[1].write(1); // Frame header
        buffer_status[1].compare_buffer_registers();
        repeat(pdcm_frames - 1) begin
            wait_for_PDCM_pulse();
            #10us;
            //#(get_period()*1us+50us);
            fork
                begin
                    for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
                        if (channels[channel]==1'b1) begin
                            repeat(packet_count)	begin
                                buffer_status[channel].write(get_word_count());
                                buffer_status[channel].validate();
                            end
                        end
                        buffer_status[channel].write(1); // Frame header for the next frame, which is not received and validated yet.
                        buffer_status[channel].compare_buffer_registers();
                    end
                end
            join_none
        end
        #(get_period()*1us+50us);
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channels[channel]==1'b1) begin
                repeat(packet_count)    begin
                    buffer_status[channel].write(get_word_count());
                    buffer_status[channel].validate();
                end
            end
            buffer_status[channel].compare_buffer_registers();
        end
    endtask
    
    virtual task read_data_packets();
        int saved_words[project_pkg::DSI_CHANNELS-1:0];
        spi_read_pdcm_frame_seq read_seq;
        int word_count = get_word_count() * packet_count + 1;
        repeat(pdcm_frames) begin
            for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
                if (channels[channel]== 1'b1) begin
                    saved_words[channel] += word_count;
                    if (saved_words[channel][15:0]<project_pkg::SIZE_DSI_PDCM_BUF) begin
                        `spi_frame_begin
                        `spi_frame_send(read_seq, channel_bits == 2'(1<<(local::channel));)
                        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                        `spi_frame_end
                        buffer_status[channel].read(word_count); //reads packet_count * word_count + frame_header
                        buffer_status[channel].compare_buffer_registers();
                    end
                    else begin
                        read_empty_packet(word_count, channel);
                    end
                end
                else begin
                    read_empty_packet(word_count, channel);
                end
            end
        end
    endtask
    
    virtual task read_empty_packet(int word_count, int channel);
        spi_read_pdcm_frame_seq read_seq;
        `spi_frame_begin
        `spi_frame_send(read_seq, channel_bits == 2'(1<<(local::channel));)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        read_seq.expect_empty(2'(channel), 0);
        buffer_status[channel].compare_buffer_registers();
    endtask
    
    virtual task create_and_initialize_buffer_status_classes(ref dsi_pdcm_data_buffer_status buffer_status[project_pkg::DSI_CHANNELS-1:0]);
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            int base_address = {16'd0, project_pkg::BASE_ADDR_DSI_PDCM_BUF[channel]};
            buffer_status[channel] = new(base_address, regmodel.DSI_PDCM_STAT[channel].ring_buffer_registers, "dsi_pdcm_data_buffer_status");
            buffer_status[channel].get_current_status();
            #1us;
        end
    endtask
    
    virtual function int get_word_count();
        int word_count;
        word_count = (int'($ceil(symbol_count/4.0))+1);
        return word_count;
    endfunction
    
    virtual function shortint get_period();
        int period;
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channels[channel]== 1'b1) begin
                period = schemes[channel].pdcm_period;
            end
        end
        return shortint'(period);
    endfunction
    
    virtual task wait_for_PDCM_pulse();
        dsi3_master_config master_config;
        for (int channel = 0; channel<project_pkg::DSI_CHANNELS; channel++) begin
            if (channels[channel] == 1'b1) begin
                master_config = get_dsi3_master_config(channel);
                break;
            end
        end
        `uvm_info(this.get_type_name(), $sformatf("WAIT FOR PULSE!"), UVM_INFO);
        @(negedge master_config.vif.cable.Voltage);
        `uvm_info(this.get_type_name(), $sformatf("GOT PULSE!"), UVM_INFO);
    endtask
    
endclass