class ecc_spi_received_data_error_seq extends ecc_error_base_seq;
    
    `uvm_object_utils(ecc_spi_received_data_error_seq)
    
    function new(string name = "");
        super.new(name);
    endfunction
    
    virtual function void initialize();
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_DATA;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_DATA;
        path = PATH_SPI_CORE_DATA_RECEIVED;
        test = "SPI received data";
        is_single_channel = 1'b1;
    endfunction
    
    virtual task apply_stimuli();
        spi_read_status_seq status_seq; 
        `spi_frame_begin
        `spi_frame_send(status_seq, )
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct==1'b1; )
        `spi_frame_end
    endtask
    
    virtual task apply_error();
        @(negedge spi.CSN);
        @(posedge spi.CSN);
        apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
        #20us;
        if (bit_error == TWO_BIT_ERR) begin
            `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
            `spi_frame_end
            check_HE_ic_status(1'b1);
            // handle CMD_IGN SPI IRQ
//            registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 1'b1);
            regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1'b1);
            registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 1'b0);
            regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC.write(status, 1'b1);
            registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
        end
        else begin
            check_HE_ic_status(1'b0);
        end
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(16)   data_error;
        uvm_hdl_data_t          data_read;
        
        if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
        `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[16-1:0]), UVM_INFO)
        data_error = new(data_read[16-1:0], bit_error);
        if (!data_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
        if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
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