class ecc_dsi3_data_high_low_error_seq extends ecc_error_base_seq;
	
    `uvm_object_utils(ecc_dsi3_data_high_low_error_seq)
    
    rand int errorInjectionTime; // 0: before CRM communication started, 1: right after data was fetched to data_high register and communication did not start yet, 2: after CRM communication started
    bit all_channels_correct = 1'b1;
    int badChannel = 0;
    
    constraint co_errorInjectionTime {soft errorInjectionTime == 1;}
    
	function new(string name = "");
		super.new(name);
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.DSI_CMD;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.DSI_CMD;
    endfunction
    
    virtual task configure_crc_setting();
        
    endtask
    
    virtual task start_crm();
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == local::all_channels_correct; bad_channel == local::badChannel;)
    endtask
	
    virtual task apply_stimuli();
        dsi3_master_tr tr;
        logic[3:0] symbol_data[$];
        dsi3_crm_packet packet;
        if(errorInjectionTime == 0) begin
            all_channels_correct = (bit_error != TWO_BIT_ERR) ? 1'b1 : 1'b0;
            badChannel = channel;
        end
        
        configure_crc_setting();
        
        `uvm_info(this.get_type_name(), $sformatf("Start data_high_low check for errorInjectionTime = %0d", errorInjectionTime), UVM_INFO)
        
        transaction_recorder.enable_recorder();
        
        start_crm();
        
        if(errorInjectionTime > 0) begin
            tr = transaction_recorder.get_last_master_tr(channel);
            if(tr != null) begin
                convert_queue#(1, 4)::convert(tr.data, symbol_data, 1); // master transaction contains data as single bits
                packet = dsi3_crm_packet::create_packet(symbol_data);
                if(packet.check_crc())begin
                    if (bit_error == TWO_BIT_ERR && errorInjectionTime == 1) begin
                        `uvm_error(this.get_type_name(), $sformatf("CRC of sent CRM data is correct. Expected CRC to be NOT correct!"))
                    end
                end
                else begin
                    if (bit_error != TWO_BIT_ERR || (errorInjectionTime == 2)) begin
                        `uvm_error(this.get_type_name(), $sformatf("CRC of sent CRM data is NOT correct. Expected CRC to be correct!"))
                    end
                end
            end
        end
        else begin
            if (bit_error == TWO_BIT_ERR) begin
                // CRM communication did not start -> remove existing CRM packets from slave to prevent data mismatch in the following CRM sequences 
                clear_slave_crm_scheme_fifo(channel);
            end
        end
        transaction_recorder.disable_recorder();
        regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN.write(status, 1'b1);
    endtask
    
    virtual task apply_error();
        if(errorInjectionTime == 0)  begin
            uvm_hdl_data_t dsi_state;
            do begin
                #5ns;
                dsi_state = hdl_read( { `STRING_OF( `LOGIC_TOP_PATH ) , $sformatf(".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.state[4:0]", channel) } );
            end while (dsi_state[4:0] != dsi3_pkg::DECODE);
        end
        else begin
            if(errorInjectionTime == 1) begin
                uvm_hdl_data_t dsi_state;
                do begin
                    #5ns;
                    dsi_state = hdl_read( { `STRING_OF( `LOGIC_TOP_PATH ) , $sformatf(".i_dsi3.generate_dsi3_blocks[%1d].i_dsi3_block.state[4:0]", channel) } );
                end while (dsi_state[4:0] != dsi3_pkg::DSI_CRM_WAIT_FOR_START);
                if(channel == 1) begin
                    #1.9us;
                end
            end
            if (errorInjectionTime == 2) begin
                #3us;
            end
        end
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(16)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[15:0]), UVM_INFO)
        data_error = new(data_read[15:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_force(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release %s failed!", path))
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
//        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_data_high_error_seq
 * 
 * sequence for applying ECC errors in DSI3 CORE data_high register
 */
class ecc_dsi3_data_high_error_seq extends ecc_dsi3_data_high_low_error_seq;
    
    `uvm_object_utils(ecc_dsi3_data_high_error_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_data_high_error_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_CORE_DATA_HIGH, channel);
        test = "DSI3 core data_high";
    endfunction
    
endclass

/**
 * Class: ecc_dsi3_data_low_error_seq
 * 
 * sequence for applying ECC errors in DSI3 CORE data_low register
 */
class ecc_dsi3_data_low_error_seq extends ecc_dsi3_data_high_low_error_seq;
    
    `uvm_object_utils(ecc_dsi3_data_low_error_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_data_low_error_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_CORE_DATA_LOW, channel);
        test = "DSI3 core data_low";
    endfunction
    
    virtual task configure_crc_setting();
        regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN.write(status, 1'b0);
    endtask
    
    virtual task start_crm();
        spi_read_crm_data_packets_seq read;
        dsi3_crm_packet packets[$];
        
        log_sim_description("single CRM transmit on all channels", LOG_LEVEL_OTHERS);
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            dsi3_crm_packet next_packet = new();
            // due to disabled crc calculation in the IC and the checks performed below, generate packets with correct crc
            if(!next_packet.randomize() with {crc_correct == 1'b1;}) `uvm_error(this.get_name(), "randomization error")
            packets.push_back(next_packet);
            add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1)));
        end
        
        check_dab(1'b1);
        
        `spi_frame_begin
        `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #500us;
        check_dab(1'b0);
        
        `spi_frame_begin
        `spi_frame_send(read, channel_bits == 2'b11;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        check_dab(1'b1);
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if ((all_channels_correct == 1'b0) && (channel == badChannel)) begin
                read.expect_empty(2'(channel));
            end
            else begin
                read.expect_flags( 2'(channel), packets[channel].crc_correct ? {} : {CRC});
                read.expect_packet(2'(channel), packets[channel]);
            end
        end
        #100us;
    endtask
    
endclass
