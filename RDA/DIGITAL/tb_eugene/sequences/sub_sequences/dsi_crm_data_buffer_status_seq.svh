class dsi_crm_data_buffer_status_seq extends base_dsi_master_seq;
    
    rand int	crm_frames;
    rand logic[project_pkg::DSI_CHANNELS-1:0] channels;
    
    constraint co_commands	{crm_frames inside {[1:10]};}
    constraint co_channels	{channels > 0; $countones(channels) > 1;}
    
    dsi_crm_data_buffer_status	buffer_status[project_pkg::DSI_CHANNELS-1:0];
    
    `uvm_object_utils(dsi_crm_data_buffer_status_seq) 
    
    function new(string name = "");
        super.new("dsi_data_buffer_status_seq");
    endfunction : new
    
    virtual task run_tests();
        channels = 2'b11;
        
        transaction_recorder.enable_recorder();
        
        check_dab(1'b1);
        
        create_and_initialize_buffer_status_classes(buffer_status);
        
        log_sim_description($sformatf("start CRM with %1d frames on channels %0b", crm_frames, channels), 2);
        
        `spi_frame_begin
        repeat(crm_frames) begin
            `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
        end
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        
        check_registers_at_each_pulse();
        
        #100us;
        
        read_data_packets();
        
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channels[channel]==1'b1)
                transaction_recorder.expect_tr_count(channel, crm_frames);
            else
                transaction_recorder.expect_tr_count(channel, 0);
        end
        
        check_dab(1'b1);
        #100us;
        
    endtask
    
    virtual task check_registers_at_each_pulse();
        repeat(crm_frames - 1) begin
            wait_for_crm_start();
            for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
                if (channels[channel]==1'b1) begin
                    buffer_status[channel].write(get_word_count());
                    buffer_status[channel].validate();
                end
                buffer_status[channel].compare_buffer_registers();
            end
        end
        #500us;
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channels[channel]==1'b1) begin
                buffer_status[channel].write(get_word_count());
                buffer_status[channel].validate();
            end
            buffer_status[channel].compare_buffer_registers();
        end
    endtask
    
    virtual task read_data_packets();
        int saved_words[project_pkg::DSI_CHANNELS-1:0];
        spi_read_crm_data_packets_seq read_seq;
        int word_count = get_word_count();
        repeat(crm_frames) begin
            for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
                if (channels[channel]== 1'b1) begin
                    saved_words[channel] += word_count;
                    if (saved_words[channel][15:0]<project_pkg::SIZE_DSI_CRM_BUF) begin
                        `spi_frame_begin
                        `spi_frame_send(read_seq, channel_bits == 2'(1<<(local::channel));)
                        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                        `spi_frame_end
                        buffer_status[channel].read(word_count);
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
        spi_read_crm_data_packets_seq read_seq;
        `spi_frame_begin
        `spi_frame_send(read_seq, channel_bits == 2'(1<<(local::channel));)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        read_seq.expect_empty(2'(channel));
        buffer_status[channel].compare_buffer_registers();
    endtask
    
    virtual task create_and_initialize_buffer_status_classes(ref dsi_crm_data_buffer_status buffer_status[project_pkg::DSI_CHANNELS-1:0]);
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            int base_address = {16'd0, project_pkg::BASE_ADDR_DSI_CRM_BUF[channel]};
            buffer_status[channel] = new(base_address, regmodel.DSI_CRM_STAT[channel].ring_buffer_registers, "dsi_crm_data_buffer_status");
            buffer_status[channel].get_current_status();
            #1us;
        end
    endtask
    
    virtual function int get_word_count();
        return 3;
    endfunction
    
    virtual task wait_for_crm_start();
        dsi3_master_config master_config;
        for (int channel = 0; channel<project_pkg::DSI_CHANNELS; channel++) begin
            if (channels[channel] == 1'b1) begin
                master_config = get_dsi3_master_config(channel);
                break;
            end
        end
        `uvm_info(this.get_type_name(), $sformatf("WAIT FOR PULSE!"), UVM_INFO);
        @(negedge master_config.vif.cable.Voltage);
        @(master_config.vif.cable.Current);
        @(negedge master_config.vif.cable.Voltage);
        `uvm_info(this.get_type_name(), $sformatf("GOT PULSE!"), UVM_INFO);
    endtask
    
endclass