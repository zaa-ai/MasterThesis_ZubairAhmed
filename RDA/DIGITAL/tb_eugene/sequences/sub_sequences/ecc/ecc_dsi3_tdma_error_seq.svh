/**
 * Class: ecc_dsi3_tdma_error_seq
 * 
 * Super sequence for applying ECC errors in DSI3 TDMA management
 * 
 * Fehler im abgelegten Datum im RAM:
 * - Periode
 * - Packet count
 * - Earliest & Latest Startzeit des jeweiligen Paketes sowie
 * - im Paket-header
 * - fsm register
 * Das ganze müsste einmal beim Validieren des Schemas sowie einmal beim PDCM mit 15 Paketen gemacht werden.
 */
class ecc_dsi3_tdma_error_seq #(int bit_width=8) extends ecc_error_base_seq;
	
    `uvm_object_param_utils(ecc_dsi3_tdma_error_seq #(bit_width))
    
    event initFinished;
	
	function new(string name = "");
		super.new(name);
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.DSI_TDMA;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.DSI_TDMA;
	endfunction
	
    virtual task apply_stimuli();
        bit all_channels_correct = (bit_error != TWO_BIT_ERR) ? 1'b1 : 1'b0;
        // invalidate any existing TDMA scheme
        `spi_frame_begin
            `spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #100us;
        ->initFinished;
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == local::all_channels_correct; bad_channel == local::channel; invalidate_tdma_scheme == 1'b1;)
    endtask
    
    virtual task apply_error();
        #360us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
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
 * Class: ecc_dsi3_pdcm_data_buffer_fsm_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA buffer FSM
 */
class ecc_dsi3_tdma_buffer_state_seq extends ecc_dsi3_tdma_error_seq#(3);
    
    `uvm_object_utils(ecc_dsi3_tdma_buffer_state_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_buffer_state_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_BUFFER_STATE, channel);
        test = "DSI3 tdma buffer FSM state";
    endfunction
    
    virtual task apply_error();
        uvm_hdl_data_t clk;
        #360us;
        do begin
            #5ns;
            clk = hdl_read( { `STRING_OF( `LOGIC_TOP_PATH ) , ".i_dsi3.clk_rst.clk" } );
        end while (clk[0]==1'b0);
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // the altered state register can lead to SRAM accesses which can lead to ECC errors in RAM (depending on the timing when the state register flips and the clock edges)
            // therefore the RAM ECC IRQ has to be handled, since its not guaranteed that the RAM ECC_IRQ will be triggered, we can't check its correct value and can only reset it:
            regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.RAM.write(status, 1'b1);
            regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.RAM.write(status, 1'b1);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_buffer_packet_index_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA buffer packet_index register
 */
class ecc_dsi3_tdma_buffer_packet_index_seq extends ecc_dsi3_tdma_error_seq#(4);
    
    `uvm_object_utils(ecc_dsi3_tdma_buffer_packet_index_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_buffer_packet_index_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_BUFFER_PACKET_INDEX, channel);
        test = "DSI3 tdma buffer packet_index";
    endfunction
    
endclass

/**
 * Class: ecc_dsi3_tdma_packet_counter_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA packet_counter register
 */
class ecc_dsi3_tdma_packet_counter_seq extends ecc_dsi3_tdma_error_seq#(4);
    
    `uvm_object_utils(ecc_dsi3_tdma_packet_counter_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_packet_counter_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_PACKET_COUNTER, channel);
        test = "DSI3 tdma packet_counter";
    endfunction
    
endclass

/**
 * Class: ecc_dsi3_tdma_state_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA state register
 */
class ecc_dsi3_tdma_state_seq extends ecc_dsi3_tdma_error_seq#(3);
    
    `uvm_object_utils(ecc_dsi3_tdma_state_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_state_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_STATE, channel);
        test = "DSI3 tdma state";
    endfunction
    
endclass

/**
 * Class: ecc_dsi3_tdma_state2branch_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA state2branch register
 */
class ecc_dsi3_tdma_state2branch_seq extends ecc_dsi3_tdma_error_seq#(3);
    
    `uvm_object_utils(ecc_dsi3_tdma_state2branch_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_state2branch_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_STATE2BRANCH, channel);
        test = "DSI3 tdma state2branch";
    endfunction
    
endclass

/**
 * Class: ecc_dsi3_tdma_writer_packet_index_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA writer packet index register
 */
class ecc_dsi3_tdma_writer_packet_index_seq extends ecc_dsi3_tdma_error_seq#(4);
    
    `uvm_object_utils(ecc_dsi3_tdma_writer_packet_index_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_writer_packet_index_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_WRITER_PACKET_INDEX, channel);
        test = "DSI3 tdma writer packet_index";
    endfunction
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #1.2us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_header_count_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info header count register
 */
class ecc_dsi3_tdma_info_header_count_seq extends ecc_dsi3_tdma_error_seq#(4);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_header_count_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_header_count_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_HEADER_COUNT, channel);
        test = "DSI3 tdma info header count";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_header_period_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info header period register
 */
class ecc_dsi3_tdma_info_header_period_seq extends ecc_dsi3_tdma_error_seq#(16);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_header_period_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_header_period_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_HEADER_PERIOD, channel);
        test = "DSI3 tdma info header period";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_next_packet_info_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info next_packet info register
 */
class ecc_dsi3_tdma_info_next_packet_info_seq extends ecc_dsi3_tdma_error_seq#(16);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_next_packet_info_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_next_packet_info_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_NEXT_PACKET_INFO, channel);
        test = "DSI3 tdma info next packet info";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_next_packet_earliest_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info next_packet earliest register
 */
class ecc_dsi3_tdma_info_next_packet_earliest_seq extends ecc_dsi3_tdma_error_seq#(16);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_next_packet_earliest_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_next_packet_earliest_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_NEXT_PACKET_EARLIEST, channel);
        test = "DSI3 tdma info next packet earliest";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_next_packet_latest_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info next_packet latest register
 */
class ecc_dsi3_tdma_info_next_packet_latest_seq extends ecc_dsi3_tdma_error_seq#(16);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_next_packet_latest_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_next_packet_latest_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_NEXT_PACKET_LATEST, channel);
        test = "DSI3 tdma info next packet latest";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_current_packet_info_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info current_packet info register
 */
class ecc_dsi3_tdma_info_current_packet_info_seq extends ecc_dsi3_tdma_error_seq#(16);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_current_packet_info_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_current_packet_info_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_CURRENT_PACKET_INFO, channel);
        test = "DSI3 tdma info current packet info";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_current_packet_earliest_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info current_packet earliest register
 */
class ecc_dsi3_tdma_info_current_packet_earliest_seq extends ecc_dsi3_tdma_error_seq#(16);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_current_packet_earliest_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_current_packet_earliest_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_CURRENT_PACKET_EARLIEST, channel);
        test = "DSI3 tdma info current packet earliest";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

/**
 * Class: ecc_dsi3_tdma_info_current_packet_latest_seq
 * 
 * sequence for applying ECC errors in DSI3 TDMA info current_packet latest register
 */
class ecc_dsi3_tdma_info_current_packet_latest_seq extends ecc_dsi3_tdma_error_seq#(16);
    
    `uvm_object_utils(ecc_dsi3_tdma_info_current_packet_latest_seq)
    
    function new(string name = "");
        super.new("ecc_dsi3_tdma_info_current_packet_latest_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        path = $sformatf(PATH_DSI3_TDMA_MANAGER_TDMA_INFO_CURRENT_PACKET_LATEST, channel);
        test = "DSI3 tdma info current packet latest";
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(bit_width)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
        data_error = new(data_read[bit_width-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task apply_error();
        @initFinished;
        if(channel == 1) begin
            // skip tmda scheme upload for channel 0
            @(negedge spi.CSN);
            repeat (8) begin
                @(posedge spi.CSN);
            end
        end
        // wait for TDMA scheme upload/validate to end
        @(negedge spi.CSN);
        repeat (8) begin
            @(posedge spi.CSN);
        end
        #2.5us;
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #150us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // Handle HW_FAIL IRQ in DSI block
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.HW_FAIL, 1'b0);
            
            // Due to invalidated TDMA scheme (or rather not correctly validated TDMA scheme the COM_ERR IRQ will be set
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b1);
            regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
            registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        if (bit_error == TWO_BIT_ERR) `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b0; bad_channel == local::channel; invalidate_tdma_scheme == 1'b0;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass