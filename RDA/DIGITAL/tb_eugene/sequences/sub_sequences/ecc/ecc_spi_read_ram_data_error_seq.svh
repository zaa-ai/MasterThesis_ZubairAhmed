/**
 * Class: ecc_spi_read_ram_data_error_seq
 * 
 * sequence for applying ecc errors while reading from RAM
 */
class ecc_spi_read_ram_data_error_seq extends ecc_error_base_seq;
    
    `uvm_object_utils(ecc_spi_read_ram_data_error_seq)
    
    event	finished_preparation;
    rand	logic[15:0]	write_data;
    
    function new(string name = "ecc_spi_read_ram_data_error");
        super.new(name);
        
    endfunction
    
    virtual function void initialize();
        is_single_channel = 1'b1;
        irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.SPI_DATA;
        irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.SPI_DATA;
        test = "Force ECC error while reading RAM with SPI register read access";
        path = "not_necessary_to_know";
    endfunction
    
    virtual task apply_stimuli();
        jtag_write_elip_seq	write;
        
        jtag_enable(.initialize_jtag(1'b1));
        #5us;
        `uvm_do_on_with(write, m_jtag_master_agent.m_sequencer, {address[15:0]==project_pkg::BASE_ADDR_RAM; data[15:0]==local::write_data; init==1'b1;})
        -> finished_preparation;
        
    endtask
    
    virtual task apply_error();
        spi_read_master_register_seq read;
        @(finished_preparation);
        #(5us);
        apply_ecc_failure();
        #10us;
        
        `spi_frame_begin
        `spi_frame_send(read, address == 0; burst_addresses.size() == 1; burst_addresses[0] == project_pkg::BASE_ADDR_RAM[11:0]; )
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        check_data(read.burst_data[0]);
        
        #10us;
        remove_ecc_failure();
        #5us;
    endtask
    
    virtual function void check_data(logic[15:0]	read_data);
        if(read_data != write_data)
            `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected 0x%4h", read_data, write_data))
    endfunction
    
    virtual task apply_ecc_failure();
        random_data_error#(6)	ecc_error;
        ecc_error = new(0, bit_error);
        if (!ecc_error.randomize()) begin
            `uvm_error(this.get_type_name(), "randomization of data_error failed")
        end
        
        #0.1us;
        test_regmodel.TEST_SRAM.SRAM_BIST_registers.SRAM_ECC_CONTROL.ELIP_ECC.write(status, ecc_error.get_data());
        
    endtask
    
    virtual task remove_ecc_failure();
        jtag_disable();
    endtask
    
    virtual task run_check_after_error();
        check_HE_ic_status(1'b0);
        `create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
    endtask
    
endclass

class ecc_spi_read_ram_data_error_with_forcing_at_fifo_seq extends ecc_spi_read_ram_data_error_seq;
    
    `uvm_object_utils(ecc_spi_read_ram_data_error_with_forcing_at_fifo_seq)
    
    function new(string name = "");
        super.new("ecc_spi_read_ram_data_error_with_forcing_at_fifo_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        test = "Force ECC error at fifo while reading RAM with SPI register read access";
        path = PATH_SPI_TX_FIFO_DATA;
    endfunction
    
    virtual task apply_stimuli();
        #1us;
        -> finished_preparation;
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(16)	data_error;
        logic[21:0]	fifo_input;
        logic[5:0]	ecc = 6'(ECC_pkg::DWF_ecc_gen_chkbits(16, 6, write_data));
        
        data_error = new(write_data, bit_error);
        if (!data_error.randomize())  `uvm_error(this.get_type_name(), "randomization of data_error failed")
        fifo_input={data_error.get_data(), ecc};
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, fifo_input), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, fifo_input), UVM_INFO)
        if (! uvm_hdl_force(path, fifo_input)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
    endtask
    
    virtual function void check_data(logic[15:0]	read_data);
        if(bit_error == TWO_BIT_ERR) begin
            if(read_data == write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected not equal to 0x%4h", read_data, write_data))
        end
        else begin
            if(read_data != write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected 0x%4h", read_data, write_data))
        end
    endfunction
    
endclass

class ecc_spi_read_ram_data_error_with_forcing_at_fifo_read_seq extends ecc_spi_read_ram_data_error_seq;
    
    `uvm_object_utils(ecc_spi_read_ram_data_error_with_forcing_at_fifo_read_seq)
    
    function new(string name = "");
        super.new("ecc_spi_read_ram_data_error_with_forcing_at_fifo_read_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        test = "Force ECC error at fifo_dout while reading RAM with SPI register read access";
        path = PATH_SPI_TX_FIFO_DOUT_DATA;
    endfunction
    
    virtual task apply_stimuli();
        #1us;
        -> finished_preparation;
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(16)  data_error;
        logic[21:0] fifo_output;
        logic[5:0]  ecc = 6'(ECC_pkg::DWF_ecc_gen_chkbits(16, 6, write_data));
        
        data_error = new(write_data, bit_error);
        if (!data_error.randomize())  `uvm_error(this.get_type_name(), "randomization of data_error failed")
        fifo_output={data_error.get_data(), ecc};
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, fifo_output), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, fifo_output), UVM_INFO)
        if (! uvm_hdl_force(path, fifo_output)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
    endtask
    
    virtual function void check_data(logic[15:0]    read_data);
        if(bit_error == TWO_BIT_ERR) begin
            if(read_data == write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected not equal to 0x%4h", read_data, write_data))
        end
        else begin
            if(read_data != write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected 0x%4h", read_data, write_data))
        end
    endfunction
    
endclass

class ecc_spi_read_ram_data_error_with_forcing_at_shift_in_seq extends ecc_spi_read_ram_data_error_seq;
    
    `uvm_object_utils(ecc_spi_read_ram_data_error_with_forcing_at_shift_in_seq)
    
    function new(string name = "");
        super.new("ecc_spi_read_ram_data_error_with_forcing_at_shift_in_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        test = "Force ECC error at shift_in while reading RAM with SPI register read access";
        path = PATH_SPI_CORE_SHIFT_IN_DATA;
        get_checker_config().enable_mirroring_check = 1'b0;
    endfunction
    
    virtual function bit get_intb_value();
        return 1'b1;
    endfunction
    
    virtual function int get_expected_irq();
        return '0;
    endfunction
    
    virtual function int get_field_mask();
        int mask;
        if (is_single_channel == 1'b1)
            mask = 0 << (irq_stat_ecc_field.get_lsb_pos());
        else
            mask = 0 << (irq_stat_ecc_field.get_lsb_pos() + channel);
        $display("mask=%4h", mask);
        return mask;
    endfunction
    
    virtual task apply_error();
        spi_read_master_register_seq read;
        spi_tx_crc_request_seq crc;
        @(finished_preparation);
        
        // invalidate any existing TDMA scheme
        `spi_frame_begin
            `spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #100us;

        fork 
            begin
                apply_ecc_failure();    
            end
            begin
                uvm_hdl_data_t  data;
                #10us;
                `spi_frame_begin
                `spi_frame_send(read, address == 0; burst_addresses.size() == 1; burst_addresses[0] == project_pkg::BASE_ADDR_RAM[11:0]; )
                `spi_frame_send(crc, mosi_crc_correct == 1'b1;)
                `spi_frame_end
                
                regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC.read(status, data);
                if(data[0] == 1'b1) begin
                    //command is incomplete due to flipped bits -> clear IRQ flag
                    regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC.write(status,1'b1);
                end
                else begin
                    check_data(read.burst_data[0]);
                end
                
                #1us;
                
                check_intb(1'b0);
                
                `spi_frame_begin
                `spi_frame_create(spi_read_status_seq, )
                `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                `spi_frame_end_with_status({NT0, NT1, SPICRC})
                
                registers.check_register(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT, 16'h8); // SPI bit should be set
                
                registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h2);
                write_and_check_irq_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h2, 16'h0000);
                
                check_intb(1'b1);
                
                #10us;
                remove_ecc_failure();
                #5us;
            end
        join;
    endtask
    
    virtual task apply_ecc_failure();
        uvm_hdl_data_t  data;
        logic shift_in;
        int randomWait;
        
        @(negedge spi.CSN);
        std::randomize (randomWait) with {randomWait > 100; randomWait < 600;};
        #(randomWait * 1ns);
        @(posedge spi.SCK);
        #1ns;
        
        if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
        else `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", path, data[15:0]), UVM_INFO)
        
        shift_in = ~data[0];
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %1b", test, shift_in), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %1b", path, shift_in), UVM_INFO)
        if (! uvm_hdl_force(path, shift_in)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        if(bit_error == TWO_BIT_ERR) begin
            @(posedge spi.SCK);
            @(posedge spi.SCK);
            #1ns;
            if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
            else `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", path, data[15:0]), UVM_INFO)
            shift_in = ~data[0];
            if (! uvm_hdl_force(path, shift_in)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
            `uvm_info(this.get_type_name(), $sformatf("force %s with %1b", test, shift_in), UVM_INFO)
            `uvm_info(this.get_type_name(), $sformatf("force %s with %1b", path, shift_in), UVM_INFO)
        end
        @(posedge spi.SCK);
        #1ns;
        remove_ecc_failure();
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
        jtag_disable();
    endtask
    
    virtual function void check_data(logic[15:0]    read_data);
        // since both cases (one-bit and two-bit errors) do not alter the read out value, this should be valid in both cases
        if(read_data != write_data)
            `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected 0x%4h", read_data, write_data))
    endfunction
    
endclass

class ecc_spi_read_ram_data_error_with_forcing_at_crc_seq extends ecc_spi_read_ram_data_error_seq;
    
    `uvm_object_utils(ecc_spi_read_ram_data_error_with_forcing_at_crc_seq)
    
    logic[15:0] crc_out;
    
    function new(string name = "");
        super.new("ecc_spi_read_ram_data_error_with_forcing_at_crc_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        test = "Force ECC error at crc while reading RAM with SPI register read access";
        path = PATH_SPI_CORE_CRC_DATA;
        get_checker_config().enable_spi_miso_crc_check = 1'b0;
    endfunction
    
    virtual function bit get_intb_value();
        return 1'b1;
    endfunction
    
    virtual function int get_expected_irq();
        return '0;
    endfunction
    
    virtual task apply_stimuli();
        #1us;
        -> finished_preparation;
    endtask
    
    virtual task apply_error();
        spi_read_master_register_seq read;
        spi_tx_crc_request_seq crc;
        @(finished_preparation);
        #(5us);
        fork 
            begin
                apply_ecc_failure();    
            end
            begin
                #10us;
                `spi_frame_begin
                `spi_frame_send(read, address == 0; burst_addresses.size() == 1; burst_addresses[0] == project_pkg::BASE_ADDR_RAM[11:0]; )
                `spi_frame_send(crc, mosi_crc_correct == 1'b1;)
                `spi_frame_end
                
                check_data(read.burst_data[0]);
                if(crc.miso_crc != crc_out) begin
                    `uvm_error(this.get_type_name(), $sformatf("read unexpected crc! read crc 0x%4h but expected 0x%4h", crc.miso_crc, crc_out))
                end
                
                #10us;
                remove_ecc_failure();
                #5us;
            end
        join;
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(16)  data_error;
        uvm_hdl_data_t  data;
        
        repeat(4) begin
            @(posedge spi.CSN);
        end
        
        write_data = data[15:0];
        if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
        else `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", path, data[15:0]), UVM_INFO)
        data_error = new(data[15:0], bit_error);
        
        if (!data_error.randomize())  `uvm_error(this.get_type_name(), "randomization of data_error failed")
        //crc_out={data_error.get_data(), ecc};
        crc_out = data_error.get_data();
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, crc_out), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, crc_out), UVM_INFO)
        if (! uvm_hdl_force(path, crc_out)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
    endtask
    
    virtual function void check_data(logic[15:0]    read_data);
        if(bit_error == TWO_BIT_ERR) begin
            if(read_data == write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected not equal to 0x%4h", read_data, write_data))
        end
        else begin
            if(read_data != write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected 0x%4h", read_data, write_data))
        end
    endfunction
    
    virtual function int get_field_mask();
        int mask;
        if (is_single_channel == 1'b1)
            mask = 0 << (irq_stat_ecc_field.get_lsb_pos());
        else
            mask = 0 << (irq_stat_ecc_field.get_lsb_pos() + channel);
        $display("mask=%4h", mask);
        return mask;
    endfunction
    
endclass

class ecc_spi_read_ram_data_error_with_forcing_ic_status_seq extends ecc_spi_read_ram_data_error_seq;
    
    `uvm_object_utils(ecc_spi_read_ram_data_error_with_forcing_ic_status_seq)
    
    logic[15:0] read_status;
    spi_status_word_flags expected_status[$];
    
    function new(string name = "");
        super.new("ecc_spi_read_ram_data_error_with_forcing_ic_status_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        test = "Force ECC error at ic_status while reading RAM with SPI register read access";
        path = PATH_SPI_CORE_IC_STATUS_DATA;
//        get_checker_config().enable_spi_miso_crc_check = 1'b0;
    endfunction
    
    virtual function bit get_intb_value();
        return 1'b1;
    endfunction
    
    virtual function int get_expected_irq();
        return '0;
    endfunction
    
    virtual task apply_error();
        spi_read_master_register_seq read;
        spi_tx_crc_request_seq crc;
        @(finished_preparation);
        #(5us);
        fork 
            begin
                apply_ecc_failure();    
            end
            begin
                #10us;
                
                checker_config::get().enable_status_word_check = 1'b0;
                `spi_frame_begin
                `spi_frame_send(read, address == 0; burst_addresses.size() == 1; burst_addresses[0] == project_pkg::BASE_ADDR_RAM[11:0]; )
                `spi_frame_create(spi_read_status_seq,)
                `spi_frame_send(crc, mosi_crc_correct == 1'b1;)
                `spi_frame_end_with_status(expected_status)
                checker_config::get().enable_status_word_check = 1'b1;
                
                check_data(read.burst_data[0]);
                //TODO: CRC!?
//                if(crc.miso_crc != crc_out) begin
//                    `uvm_error(this.get_type_name(), $sformatf("read unexpected crc! read crc 0x%4h but expected 0x%4h", crc.miso_crc, crc_out))
//                end
                
                #10us;
                remove_ecc_failure();
                #5us;
            end
        join;
    endtask
    
    virtual task apply_ecc_failure();
        random_data_error#(16)  data_error;
        uvm_hdl_data_t  data;
        
        @(negedge spi.CSN);
        
        if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
        else `uvm_info(this.get_type_name(), $sformatf("read %s with %2h", path, data[15:0]), UVM_INFO)
        data_error = new(data[15:0], bit_error);
        
        if (!data_error.randomize())  `uvm_error(this.get_type_name(), "randomization of data_error failed")
        read_status = data_error.get_data();
        for (int i = 0; i < 16; i++) begin
            if(read_status[i] == 1'b1) begin
                expected_status.push_back(spi_status_word_flags'(i));
            end
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, read_status), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, read_status), UVM_INFO)
        if (! uvm_hdl_force(path, read_status)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
        jtag_disable();
    endtask
    
    virtual function void check_data(logic[15:0]    read_data);
        if(bit_error == TWO_BIT_ERR) begin
            if(read_data == write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected not equal to 0x%4h", read_data, write_data))
        end
        else begin
            if(read_data != write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected 0x%4h", read_data, write_data))
        end
    endfunction
    
    virtual function int get_field_mask();
        int mask;
        if (is_single_channel == 1'b1)
            mask = 0 << (irq_stat_ecc_field.get_lsb_pos());
        else
            mask = 0 << (irq_stat_ecc_field.get_lsb_pos() + channel);
        $display("mask=%4h", mask);
        return mask;
    endfunction
    
endclass

class ecc_spi_read_ram_data_error_with_forcing_at_shift_out_seq extends ecc_spi_read_ram_data_error_seq;
    
    `uvm_object_utils(ecc_spi_read_ram_data_error_with_forcing_at_shift_out_seq)
    
    function new(string name = "");
        super.new("ecc_spi_read_ram_data_error_with_forcing_at_shift_out_seq");
    endfunction
    
    virtual function void initialize();
        super.initialize();
        test = "Force ECC error at shift_out while reading RAM with SPI register read access";
        path = PATH_SPI_CORE_SHIFT_OUT_DATA;
    endfunction
    
    virtual task apply_error();
        spi_read_master_register_seq read;
        spi_tx_crc_request_seq crc;
        @(finished_preparation);
        #(5us);
        fork 
            begin
                apply_ecc_failure();    
            end
            begin
                #10us;
                
                `spi_frame_begin
                `spi_frame_send(read, address == 0; burst_addresses.size() == 1; burst_addresses[0] == project_pkg::BASE_ADDR_RAM[11:0]; )
                `spi_frame_send(crc, mosi_crc_correct == 1'b1;)
                `spi_frame_end
                
                check_data(read.burst_data[0]);
                
                #10us;
                remove_ecc_failure();
                #5us;
            end
        join;
    endtask
    
    virtual task apply_ecc_failure();
        int randomWait, secondBit;
        logic[15:0] shift_out;
        uvm_hdl_data_t  data;
        
        @(negedge spi.CSN);
        @(negedge spi.CSN);
        @(negedge spi.CSN);
        @(negedge spi.CSN);
        std::randomize (randomWait) with {randomWait >= 0; randomWait < 16;};
        `uvm_info(this.get_type_name(), $sformatf("random wait = %0d", randomWait), UVM_INFO)
        repeat(randomWait) begin
            @(posedge spi.SCK);
        end
        #1ns;
        
        if (!uvm_hdl_read(path, data)) `uvm_error(this.get_type_name(), $sformatf("reading of %s failed", path))
        else `uvm_info(this.get_type_name(), $sformatf("read %s with %0h", path, data[15:0]), UVM_INFO)
        
        shift_out = data[15:0];
        shift_out[randomWait] = ~shift_out[randomWait];
        if(bit_error == TWO_BIT_ERR) begin
            std::randomize (secondBit) with {secondBit >= 0; secondBit < 16; secondBit != randomWait;};
            shift_out[secondBit] = ~shift_out[secondBit];
        end
        
        `uvm_info(this.get_type_name(), $sformatf("force %s with %0h", test, shift_out), UVM_INFO)
        `uvm_info(this.get_type_name(), $sformatf("force %s with %0h", path, shift_out), UVM_INFO)
        if (! uvm_hdl_deposit(path, shift_out)) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
        
        @(posedge spi.SCK);
        #1ns;
        remove_ecc_failure();
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release on %s failed!", path))
        jtag_disable();
    endtask
    
    virtual function void check_data(logic[15:0]    read_data);
        if(bit_error == TWO_BIT_ERR) begin
            if(read_data == write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected not equal to 0x%4h", read_data, write_data))
        end
        else begin
            if(read_data != write_data)
                `uvm_error(this.get_type_name(), $sformatf("read unexpected data! read 0x%4h but expected 0x%4h", read_data, write_data))
        end
    endfunction
    
endclass
