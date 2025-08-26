`include "svunit_defines.svh"
`include "clk_rst_define.sv"

module spi_test import project_pkg::*; ();
    
    `include "uvm_macros.svh"
    
    import svunit_pkg::svunit_testcase;
    import crc_calculation_pkg::*;
    import common_env_pkg::*;
    import addresses_pkg::*;
    import common_test_pkg::*;
    import uvm_pkg::*;
    import spi_unit_test_pkg::*;
    import spi_pkg::*;
    import svunit_uvm_mock_pkg::*;
    import elip_bus_pkg::*;
    
    string name = "spi_test";
    svunit_testcase svunit_ut;
    
    spi_sequencer	sequencer;
    
    top_config		_top_config;
    spi_if			spi_if_agent();
    spi_int_if		spi_if_dut();
    elip_bus_sequencer_t	elip_sequencer;
    
    elip_full_if	elip_read ();
    elip_bus_if		elip_read_register_bus();
    elip_bus_if		elip_registers_bus();
    elip_if #(16, 16) elip_registers();
    
    elip_full_if	elip_crm_buffer[DSI_CHANNELS-1:0] ();
    elip_full_if	elip_pdcm_buffer[DSI_CHANNELS-1:0] ();
    
    spi_status_if 	spi_status ();
    
    `clk_def(27777ps)
    
    ecc_error_if #(.WIDTH (1)) core_ecc_error ();
    ecc_error_if #(.WIDTH (1)) data_reader_ecc_error ();
    
    buffer_writer_if	    command_writer();
    buffer_reader_if	    dsi3_pdcm_data_reader();
    buffer_reader_if	    dsi3_crm_data_reader();
    buffer_writer_if	    dsi3_crm_data_writer[DSI_CHANNELS-1:0]();
    pdcm_buffer_writer_if	dsi3_pdcm_data_writer[DSI_CHANNELS-1:0]();
    
    logic	interrupt, clear_command_queue;
    elip_data_t		elip_data_read, elip_crm_data_read[DSI_CHANNELS-1:0], elip_pdcm_data_read[DSI_CHANNELS-1:0], elip_data;
    
    // interface mapping between SPI agent and DUT
    assign	spi_if_dut.csb = spi_if_agent.CSN;
    assign	spi_if_dut.csb_resn = ~spi_if_agent.CSN;
    assign	spi_if_dut.sck = spi_if_agent.SCK;
    assign	spi_if_dut.sdi = spi_if_agent.SDI;
    assign	spi_if_agent.SDO = spi_if_dut.sdo;
    
    logic[1:0]	dsi3_pdcm_data_read_channel_select;
    logic[1:0]	dsi3_crm_data_read_channel_select;
    data_t      tdma_frame_word_count[DSI_CHANNELS-1:0];
    
    ecc_error_if #(.WIDTH(1)) ecc_error_crm[DSI_CHANNELS-1:0]();
    ecc_error_if #(.WIDTH(1)) ecc_error_pdcm[DSI_CHANNELS-1:0] ();
    
    buffer_reader_if	dsi3_crm_data_readers[DSI_CHANNELS-1:0] ();
    buffer_reader_if	dsi3_pdcm_data_readers[DSI_CHANNELS-1:0] ();
    
    initial begin
        _top_config = new("_top_config");
        uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
        uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
        
        _top_config._spi_config.vif	= spi_if_agent; 
        _top_config._buffer_writer_config.vif = command_writer;
        _top_config._buffer_writer_config.vif_clk_rst = clk_rst;
        _top_config._elip_config.vif = elip_read_register_bus;
        _top_config._elip_registers_config.vif = elip_registers_bus;
        for (int l=0; l<DSI_CHANNELS; l++) begin
            _top_config._crm_buffer_writer_config[l].vif_clk_rst = clk_rst;
            _top_config._pdcm_buffer_writer_config[l].vif_clk_rst = clk_rst;
        end
        _top_config._crm_buffer_writer_config[0].vif = dsi3_crm_data_writer[0];
        _top_config._crm_buffer_writer_config[1].vif = dsi3_crm_data_writer[1];
        _top_config._pdcm_buffer_writer_config[0].vif = dsi3_pdcm_data_writer[0];
        _top_config._pdcm_buffer_writer_config[1].vif = dsi3_pdcm_data_writer[1];
        
        run_test();
        
        _top_config._spi_config.cycle_time			  = 1.0us/20.0;
        _top_config._spi_config.inter_word_gap        = 0.0ns;
        _top_config._spi_config.csn_to_sck            = 5ns;
        _top_config._spi_config.sck_to_csn            = 5ns;
    end
    
    //===================================
    // This is the UUT that we're 
    // running the Unit Tests on
    //===================================
    logic   ram_initialized;
    spi #(.ADDR_WIDTH (16)) i_spi (
        .clk_rst         (clk_rst.slave        ), 
        .spi_int         (spi_if_dut.slave     ), 
        .elip_spi_read   (elip_read.master), 
        .command_writer  (command_writer.master ),
        .spi_status      (spi_status.spi     ),
        .elip_registers  (elip_registers.slave  ), 
        .o_elip_data_read(elip_data_read ), 
        .o_interrupt     (interrupt      ),   
        .spi_ecc_error   (core_ecc_error.master     ),
        .data_reader_ecc_error (data_reader_ecc_error.master     ),
        .i_clear_command_queue(clear_command_queue),
        .i_write_not_allowed  (1'b0),
        .i_tdma_frame_word_count(tdma_frame_word_count),
        .i_ram_initialized(ram_initialized),
        .dsi3_pdcm_data_reader               (dsi3_pdcm_data_reader.master      ),
        .dsi3_crm_data_reader                (dsi3_crm_data_reader.master       ),
        .o_dsi3_pdcm_data_read_channel_select(dsi3_pdcm_data_read_channel_select),
        .o_dsi3_crm_data_read_channel_select (dsi3_crm_data_read_channel_select )
    );
    
    always_comb begin
        elip_data = elip_data_read;
        for (int i=0; i<DSI_CHANNELS; i++) begin
            elip_data |= elip_crm_data_read[i];
            elip_data |= elip_pdcm_data_read[i];
        end
    end
    
    interface_converter_elip_full_2_elip_bus i_interface_converter_read_data (
        .clk_rst    (clk_rst.slave             ),
        .elip_full  (elip_read.slave       ), 
        .elip_bus   (elip_read_register_bus  ));
    
    interface_converter_elip_bus_2_elip #(.data_width(16)) i_interface_converter_elip_bus_2_elip (
        .clk_rst     (clk_rst.slave              ), 
        .elip_bus    (elip_registers_bus   ), 
        .elip        (elip_registers.master       ), 
        .i_data_out  (elip_data       ));
    
    buffer_reader_demux i_crm_buffer_reader_demux (
        .reader        (dsi3_crm_data_reader.slave        ),
        .readers       (dsi3_crm_data_readers.master       ),
        .channel_select(dsi3_crm_data_read_channel_select)
    );
    
    buffer_reader_demux i_pdcm_buffer_reader_demux (
        .reader        (dsi3_pdcm_data_reader.slave        ),
        .readers       (dsi3_pdcm_data_readers.master       ),
        .channel_select(dsi3_pdcm_data_read_channel_select)
    );
    
    elip_full_if elip_tdma[DSI_CHANNELS-1:0] ();
    
    register_read_model i_register_read_model (
        .clk_rst  (clk_rst.slave ), 
        .elip     (elip_read.slave    ));
    
    generate
        genvar k;
        for (k=0; k < DSI_CHANNELS; k++) begin : generate_buffers
            buffer #(
                .BASE_ADDR            (BASE_ADDR_DSI_CRM_STAT[k] ),
                .ADDR_WIDTH           (ELIP_ADDR_WIDTH           ),
                .BUFFER_OFFSET_ADDRESS(BASE_ADDR_DSI_CRM_BUF[k]  ),
                .BUFFER_SIZE          (SIZE_DSI_CRM_BUF          ),
                .PRIORITY_READ        (1'b1        )
            ) i_crm_buffer (
                .clk_rst                  (clk_rst.slave                  ),
                .reader                   (dsi3_crm_data_readers[k].slave     ),
                .writer                   (dsi3_crm_data_writer[k].slave     ),
                .elip                     (elip_crm_buffer[k].master         ),
                .elip_registers           (elip_registers.slave     ),
                .o_elip_registers_data_out(elip_crm_data_read[k]),
                .o_data_available         (         ),
                .ecc_error                (ecc_error_crm[k].master        )
            );
            
            ram_model #(.RAM_SIZE(SIZE_DSI_CRM_BUF), .OFFSET(BASE_ADDR_DSI_CRM_BUF[k])) i_crm_ram_model (
                .clk_rst(clk_rst.slave),
                .elip   (elip_crm_buffer[k].slave   )
            );
            
            pdcm_buffer #(
                .BASE_ADDR            (BASE_ADDR_DSI_PDCM_STAT[k] ),
                .ADDR_WIDTH           (ELIP_ADDR_WIDTH           ),
                .BUFFER_OFFSET_ADDRESS(BASE_ADDR_DSI_PDCM_BUF[k]  ),
                .BUFFER_SIZE          (SIZE_DSI_PDCM_BUF          ),
                .PRIORITY_READ        (1'b1        )
            ) i_pdcm_buffer (
                .clk_rst                  (clk_rst.slave                  ),
                .reader                   (dsi3_pdcm_data_readers[k].slave     ),
                .writer                   (dsi3_pdcm_data_writer[k].slave     ),
                .elip                     (elip_pdcm_buffer[k].master         ),
                .elip_registers           (elip_registers.slave     ),
                .o_elip_registers_data_out(elip_pdcm_data_read[k]),
                .o_data_available         (         ),
                .ecc_error                (ecc_error_pdcm[k].master        )
            );
            
            ram_model #(.RAM_SIZE(SIZE_DSI_PDCM_BUF), .OFFSET(BASE_ADDR_DSI_PDCM_BUF[k])) i_pdcm_ram_model (
                .clk_rst(clk_rst.slave),
                .elip   (elip_pdcm_buffer[k].slave   )
            );
            
        end
    endgenerate
    
    initial initialize();
    
    function automatic void initialize();
        ram_initialized = 1'b1;
        spi_status.buffer_fill_warning = '0;
        spi_status.clkref_failure = 1'b0;
        spi_status.dsi3_crm_data_available = '0;
        spi_status.dsi3_pdcm_data_available = '0;
        spi_status.dsi3_hardware_error = 1'b0;
        spi_status.ldo_uv = 1'b0;
        spi_status.overtemperature = 1'b0;
        spi_status.vcc_uv = 1'b0;
        spi_status.ecc_failure = 1'b0;
        spi_status.otp_fail = 1'b0;
        spi_status.vrr_nok = 1'b0;
        spi_status.hardware_fail_dsi3 = '0;
        spi_status.hardware_fail_main_control = '0;
        spi_status.no_tdma_scheme_defined = '0;
        clear_command_queue = 1'b0;
        foreach(tdma_frame_word_count[i])
            tdma_frame_word_count[i] = '0;
    endfunction
    
    //===================================
    // Build
    //===================================
    function void build();
        svunit_ut = new(name);
    endfunction
    
    //===================================
    // Setup for running the Unit Tests
    //===================================
    task setup();
        svunit_ut.setup();
        /* Place Setup Code Here */
        uvm_report_mock::setup();
        initialize();
        _top_config._buffer_comparator.flush();
        _top_config._check_register_reads.initialize();
        #1us;
    endtask
    
    //===================================
    // Here we deconstruct anything we 
    // need after running the Unit Tests
    //===================================
    task teardown();
        svunit_ut.teardown();
        /* Place Teardown Code Here */
        #0.1us;
        write_elip(ADDR_SPI_SPI_IRQ_STAT, 16'hffff);
        #0.1us;
    endtask
    
    //===================================
    // All tests are defined between the
    // SVUNIT_TESTS_BEGIN/END macros
    //
    // Each individual test must be
    // defined between `SVTEST(_NAME_)
    // `SVTEST_END
    //
    // i.e.
    //	 `SVTEST(mytest)
    //		 <test code>
    //	 `SVTEST_END
    //===================================
    
    
    /*###   other tasks   ######################################################*/
    task _wait(input int wait_cycles=2);
        wait_for_n_clocks(wait_cycles);
    endtask
    
    task automatic read_elip (input elip_addr_t address, output data_t data);
        elip_bus_seq	seq = new();
        elip_tr			tr = new();
        void'(tr.randomize with {write == 1'b0; address == local::address;});
        seq.req= tr;
        seq.start(elip_sequencer);
        data = seq.req.data_read;
    endtask
    
    task automatic write_elip(input elip_addr_t address, input data_t data);
        elip_bus_seq	seq = new();
        elip_tr			tr = new();
        void'(tr.randomize with {write == 1'b1; address == local::address; data_write == local::data;});
        seq.req= tr;
        seq.start(elip_sequencer);
        @(posedge clk_rst.clk);
    endtask
    
    task automatic read_status(output SPI_IRQ_STAT_t stat);
        data_t			read_data;
        read_elip(ADDR_SPI_SPI_IRQ_STAT, read_data);
        stat = read_data;
    endtask
    
    function automatic int get_errors();
        int errors = 0;
        errors += _top_config._buffer_comparator.m_mismatches;
        if ((_top_config._buffer_comparator.check_for_empty() == 1'b0)) begin
            errors++;
        end
        errors += _top_config._check_register_reads.get_error_count();
        errors += (!uvm_report_mock::verify_complete()) ? 1 : 0;
        return errors;
    endfunction
    
    function automatic bit check_status(spi_command_frame_seq frame, spi_status_word_flags status_flags[$]);
        bit error;
        flags_container #(spi_status_word_flags) flags = new();
        flags.set_flags(status_flags);
        error = frame.status.check_flags_are_equal(flags, $sformatf("Unexpected SPI status word flags")); 
        return error;
    endfunction
    
    function automatic data_ecc_t get_data_with_ecc(data_t data);
        data_ecc_t data_ecc;
        data_ecc.data = data;
        // @SuppressProblem -type assign_truncation_non_const_other -count 1 -length 1
        data_ecc.ecc = DWF_ecc_gen_chkbits(16, 6, data);
        return data_ecc;
    endfunction
    
    function automatic int get_word_count_of_scheme(tdma_scheme_pdcm scheme);
        int words = 1;
        foreach(scheme.packets[i]) begin
            words++;
            words += scheme.packets[i].get_word_count_of_data();
        end
        return words;
    endfunction
    
    function automatic void write_scheme_to_buffer(int channels[$], tdma_scheme_pdcm scheme);
        automatic int index = 0;
        foreach(channels[index]) begin
            tdma_frame_word_count[channels[index]] = get_word_count_of_scheme(scheme);
        end
    endfunction
    
    function automatic void fill_scheme_with_data(tdma_scheme_pdcm scheme);
        foreach(scheme.packets[i]) begin
            dsi3_packet packet = scheme.packets[i].packet;
            while (packet.data.size < scheme.packets[i].symbol_count)
                packet.data.push_back($urandom());
        end
    endfunction
    
    task automatic write_data_to_pdcm_buffer(int channels[$], tdma_scheme_pdcm scheme, output spi_read_pdcm_frame_seq pdcm_read);
        pdcm_read = new();
        pdcm_read.data_out.delete();
        repeat(2) pdcm_read.data_out.push_back('0);
        foreach(channels[i])
            _top_config._pdcm_packet_creator[i].add_frame(scheme, pdcm_read.data_out);
    endtask
    
    //FIXME: add check for not receiving a SPI frame!!
    
    /* FIXME: add test cases
     *  - abort reading of READ_PACKET in last packet
     *  - abort reading of READ_PACKET in first packet (when trying to read 2)
     */
    
    /*###   test cases   ######################################################*/
    
    `SVUNIT_TESTS_BEGIN
    enable_clk = 1'b1;
    #10us;
    sequencer = _top_config._spi_agent.m_sequencer;
    elip_sequencer	 = _top_config._elip_registers_agent.m_sequencer;
    
    
    /*###   general test cases   ######################################################*/
    begin : general_tests
        
        for (int i=0; i<10; i++) begin
            spi_command_frame_seq	seq;
            `SVTEST ($sformatf("%2d: Check written buffer", i))
            seq = spi_test_seq::create_test_seq(sequencer);
            spi_test_seq::append_crc_command(seq);
            seq.start(sequencer);
            #10us;
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        for (int i=0; i<10; i++) begin
            spi_command_frame_seq	seq;
            `SVTEST ($sformatf("%2d: Check written buffer with CRC errors", i))
            seq = spi_test_seq::create_test_frame(sequencer);
            spi_test_seq::append_crc_command(seq);
            seq.start(sequencer);
            #10us;
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        for (int i=0; i<10; i++) begin
            spi_command_frame_seq	seq;
            `SVTEST ($sformatf("%2d: Check written buffer with CRC errors", i))
            seq = spi_test_seq::create_test_frame(sequencer, $urandom_range(15,5));
            spi_test_seq::append_crc_command(seq);
            seq.start(sequencer);
            #10us;
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        `SVTEST ($sformatf("Check register read access via ELIP"))
            spi_command_frame_seq read; 
            read = spi_test_seq::create_register_read(sequencer, 1);
            read.start(sequencer);
            #10us;
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("Check register read access via ELIP - burst read"))
            spi_command_frame_seq read;
            read = spi_test_seq::create_register_read(sequencer, 10);
            read.start(sequencer);
            #10us;
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("Check register write access via ELIP"))
            spi_command_frame_seq write;
            write = spi_frame_factory #(0)::create_frame_with_write_register_commands(sequencer, 1);
            spi_test_seq::append_crc_command(write);
            write.start(sequencer);
            #10us;
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("Check multiple register write access via ELIP"))
            spi_command_frame_seq write;
            write = spi_frame_factory #(0)::create_frame_with_write_register_commands(sequencer);
            spi_test_seq::append_crc_command(write);
            write.start(sequencer);
            #10us;
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("Check CRC error flag"))
            bit error;
            spi_command_frame_seq	frame;
            frame = spi_frame_factory::create_random_frame_with_queue_commands(sequencer, $urandom_range(15,5));
            spi_test_seq::append_crc_command_with(.crc_correct(1'b0), .frame(frame));
            frame.start(sequencer);
            #1us;
            frame = spi_test_seq::create_register_read(sequencer, 1);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            error = check_status(frame, {SPICRC});
            #1us;
            frame = spi_test_seq::create_register_read(sequencer, 1);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            error |= check_status(frame, {SPICRC});
            `FAIL_UNLESS_EQUAL(error, 1'b0)
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("Check CRC error interrupt"))
            bit error;
            spi_command_frame_seq	frame;
            spi_command_frame_seq	frame2;
            SPI_IRQ_STAT_t	irq_stat;
            SPI_IRQ_MASK_t	irq_mask;
            
            irq_mask = '1; 
            
            write_elip(ADDR_SPI_SPI_IRQ_STAT, 16'hffff);
            read_status(irq_stat);
            `FAIL_UNLESS_EQUAL(interrupt, 1'b0);
            `FAIL_UNLESS_EQUAL(irq_stat, '0);
            
            frame = spi_frame_factory::create_random_frame_with_queue_commands(sequencer, $urandom_range(15,5));
            spi_test_seq::append_crc_command_with(.crc_correct(1'b0), .frame(frame));
            frame.start(sequencer);
            #1us;
            `FAIL_UNLESS_EQUAL(interrupt, 1'b1);
            read_status(irq_stat);
            `FAIL_UNLESS_EQUAL(irq_stat.CRC_ERR, 1'b1);
            
            read_elip(ADDR_SPI_SPI_IRQ_MASK, irq_mask);
            irq_mask.CRC_ERR = 1'b0;
            write_elip(ADDR_SPI_SPI_IRQ_MASK, irq_mask);
            `FAIL_UNLESS_EQUAL(interrupt, 1'b0);
            irq_mask.CRC_ERR = 1'b1;
            write_elip(ADDR_SPI_SPI_IRQ_MASK, irq_mask);
            `FAIL_UNLESS_EQUAL(interrupt, 1'b1);
            
            read_status(irq_stat);
            `FAIL_UNLESS_EQUAL(irq_stat.CRC_ERR, 1'b1);
            
            write_elip(ADDR_SPI_SPI_IRQ_STAT, 16'hffff);
            `FAIL_UNLESS_EQUAL(interrupt, 1'b0);
            read_elip(ADDR_SPI_SPI_IRQ_STAT, irq_stat);
            `FAIL_UNLESS_EQUAL(irq_stat, '0);
            
            frame2 = spi_test_seq::create_register_read(sequencer, 1);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame2));
            frame2.start(sequencer);
            error = check_status(frame2, {});
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
            
            frame.start(sequencer);
            #1us;
            frame2.start(sequencer);
            error |= check_status(frame2, {SPICRC});
            write_elip(ADDR_SPI_SPI_IRQ_STAT, 16'hffff);
            `FAIL_UNLESS_EQUAL(interrupt, 1'b0);
            
            frame2.start(sequencer);
            error = check_status(frame2, {});
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `FAIL_UNLESS_EQUAL(error, 1'b0)
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        for (int i=0; i<50; i++) begin
            `SVTEST ($sformatf("Check CSB pulsing without data (%1d)",i))
                bit error;
                // in 521.44 nothing will happen
                spi_command_frame_seq	frame = new();
                spi_crm_seq	crm_seq = new();
                
                spi_if_agent.CSN = 1'b0;
                #0.1us;
                spi_if_agent.CSN = 1'b1;
                #1us;
                
                void'(crm_seq.randomize with {channel_bits == 2'b11; broad_cast == 1'b0;});
                frame.add_command(crm_seq);
                
                spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
                frame.start(sequencer);
                #2us;
                
                error = check_status(frame, {});
                `FAIL_UNLESS_EQUAL(error, 1'b0)
                `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        `SVTEST ($sformatf("incomplete register read (one word only)"))
            spi_any_command_seq any_seq = new();
            spi_command_frame_seq frame = new();
            logic [15:0] miso_crc_calculated;
            
            any_seq.command_words.push_back(16'h2020); // reg read
            any_seq.command_words.push_back(16'h1234); // CRC command
            any_seq.command_words.push_back(16'h268E); // MOSI CRC
            any_seq.command_words.push_back(16'h1234); // CRC command
            any_seq.command_words.push_back(16'h0EC9); // MOSI CRC
            frame.add_command(any_seq);
            
            frame.start(sequencer);
            #2us;
            // check 1st MISO CRC
            miso_crc_calculated = crc_calculation_pkg::spi_calculate_correct_crc('{16'h0000, 16'h2020});
            `FAIL_UNLESS_EQUAL(any_seq.data_out[2], miso_crc_calculated)
            // check IC status
            `FAIL_UNLESS_EQUAL(any_seq.data_out[3], 16'h2000) // CMD_INC 
            // check 2nd MISO CRC
            `FAIL_UNLESS_EQUAL(any_seq.data_out[4], 16'h1be9) 
            
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
    end
    
    /*###   CRM   ######################################################*/
    begin : spi_crm_tests
        `SVTEST ($sformatf("CRM read"))
            spi_dsi_data_packet packet = spi_dsi_data_packet::create_packet(0, 8, '{16'h0BAD, 16'hC0DE}, '{});
            spi_command_frame_seq frame = new();
            spi_read_crm_data_packets_seq	read_crm = new();
            _top_config._crm_packet_creator[0].add_packet(packet);
            #1us;
            void'(read_crm.randomize() with {channel_bits == 2'd1;});
            frame.add_command(read_crm);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            read_crm.expect_spi_data_packet(0,packet);
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("CRM read - on both channels"))
            spi_command_frame_seq frame = new();
            spi_read_crm_data_packets_seq	read_crm = new();
            spi_dsi_data_packet packets[2];
            packets[0] = spi_dsi_data_packet::create_packet(0, 8, '{16'hCAFE, 16'hAFFE}, '{TE});
            packets[1] = spi_dsi_data_packet::create_packet(1, 8, '{16'h0BAD, 16'hC0DE}, '{CRC});
            foreach (packets[i])
                _top_config._crm_packet_creator[i].add_packet(packets[i]);
            #1us;
            void'(read_crm.randomize() with {channel_bits == 2'b11;});
            frame.add_command(read_crm);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            foreach (packets[i])
                read_crm.expect_spi_data_packet(i,packets[i]);
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("CRM read - read two times on one channel"))
            spi_command_frame_seq frame = new();
            spi_dsi_data_packet packets[2];
            spi_read_crm_data_packets_seq	read_crm[2];
            packets[0] = spi_dsi_data_packet::create_packet(0, 8, '{16'h1234, 16'h5678}, '{VE});
            packets[1] = spi_dsi_data_packet::create_packet(0, 8, '{16'h90AB, 16'hCDEF}, '{SE});
            foreach (packets[i])
                _top_config._crm_packet_creator[0].add_packet(packets[i]);
            #1us;
            foreach (read_crm[i]) begin
                read_crm[i] = new();
                void'(read_crm[i].randomize() with {channel_bits == 2'b01;});
                frame.add_command(read_crm[i]);
            end
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            foreach (packets[i])
                read_crm[i].expect_spi_data_packet(0,packets[i]);
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("CRM read - read with only one word stored"))
            spi_dsi_data_packet packet = spi_dsi_data_packet::create_packet(0, 4, '{16'h89f2}, '{SCE});
            spi_command_frame_seq frame = new();
            spi_read_crm_data_packets_seq	read_crm = new();
            _top_config._crm_packet_creator[1].add_packet(packet);
            #1us;
            void'(read_crm.randomize() with {channel_bits == 2'b10;});
            frame.add_command(read_crm);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            read_crm.expect_spi_data_packet(1, packet);
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        for (int channels = 0; channels < (1<<DSI_CHANNELS); channels++) begin
            
            `SVTEST ($sformatf("CRM read on %2b - empty data", channels))
                spi_dsi_data_packet packet = spi_dsi_data_packet::create_packet(0, 0, '{}, '{});
                spi_command_frame_seq frame = new();
                spi_read_crm_data_packets_seq	read_crm = new();
                //    			_top_config._crm_packet_creator[0].add_packet(packet);
                //    			_top_config._crm_packet_creator[1].add_packet(packet);
                #1us;
                void'(read_crm.randomize() with {channel_bits == local::channels;});
                frame.add_command(read_crm);
                spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
                frame.start(sequencer);
                #1us;
                for (int i = 0; i < (DSI_CHANNELS); i++) begin
                    if (channels[i] == 1'b1)
                        read_crm.expect_spi_data_packet(i,packet);
                end
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
    end
    
    begin : spi_status_tests
        /*###   SPI status   ######################################################*/
        `SVTEST ($sformatf("SPI status - initial"))
            bit error;
            spi_command_frame_seq frame = new();
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            error = check_status(frame, {});
            `FAIL_UNLESS_EQUAL(error, 1'b0)
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        for (int dap = 0; dap < 1<<(DSI_CHANNELS-1); dap++) begin
            `SVTEST ($sformatf("SPI status - PDCM data available(b%1b", dap[1:0]))
                bit error;
                spi_status_word_flags status_flags[$];
                spi_command_frame_seq frame = new();
                spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
                spi_status.dsi3_pdcm_data_available = dap;
                #1us;
                frame.start(sequencer);
                #1us;
                if(dap[0])  status_flags.push_back(PD0);
                if(dap[1])  status_flags.push_back(PD1);
                error = check_status(frame, status_flags);
                `FAIL_UNLESS_EQUAL(error, 1'b0)
                `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        for (int dac = 0; dac < 1<<(DSI_CHANNELS-1); dac++) begin
            `SVTEST ($sformatf("SPI status - CRM data available(b%1b", dac[1:0]))
                bit error;
                spi_status_word_flags status_flags[$];
                spi_command_frame_seq frame = new();
                spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
                spi_status.dsi3_crm_data_available = dac;
                #1us;
                frame.start(sequencer);
                #1us;
                if(dac[0])  status_flags.push_back(CR0);
                if(dac[1])  status_flags.push_back(CR1);
                error = check_status(frame, status_flags);
                `FAIL_UNLESS_EQUAL(error, 1'b0)
                `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        for (int ntsd = 0; ntsd < 1<<(DSI_CHANNELS-1); ntsd++) begin
            `SVTEST ($sformatf("SPI status - no TDMA scheme defined(b%1b", ntsd[1:0]))
                bit error;
                spi_status_word_flags status_flags[$];
                spi_command_frame_seq frame = new();
                spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
                spi_status.no_tdma_scheme_defined = ntsd;
                #1us;
                frame.start(sequencer);
                #1us;
                if(ntsd[0])  status_flags.push_back(NT0);
                if(ntsd[1])  status_flags.push_back(NT1);
                error = check_status(frame, status_flags);
                `FAIL_UNLESS_EQUAL(error, 1'b0)
                `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        `define test_spi_status(_text_, _if_field_, _flags_) `SVTEST ($sformatf(_text_)) \
            bit error; \
            spi_command_frame_seq frame = new(); \
            checker_config::get().enable_hardware_error_check = 1'b0; \
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame)); \
            spi_status.``_if_field_ = 1'b1; \
            #1us; \
            frame.start(sequencer); \
            #1us; \
            error = check_status(frame, _flags_); \
            checker_config::get().enable_hardware_error_check = 1'b1; \
            `FAIL_UNLESS_EQUAL(error, 1'b0) \
            `FAIL_UNLESS_EQUAL(get_errors(), 0) \
        `SVTEST_END
        
        `test_spi_status("SPI status - CLKREF failure",     clkref_failure, {HE})
        `test_spi_status("SPI status - Overtemperature",    overtemperature, {HE})
        `test_spi_status("SPI status - DSI3 hardware error", dsi3_hardware_error, {HE})
        `test_spi_status("SPI status - buffer fill warning", buffer_fill_warning, {BF})
        `test_spi_status("SPI status - VCC UV", vcc_uv, {HE})
        `test_spi_status("SPI status - LDO UV", ldo_uv, {HE})
        `test_spi_status("SPI status - VRR NOK", vrr_nok, {HE})
        `test_spi_status("SPI status - ECC failure", ecc_failure, {HE})
        `test_spi_status("SPI status - OTP fail", otp_fail, {HE})
        `test_spi_status("SPI status - hardware failure main control", hardware_fail_main_control, {HE})
        
    end
    
    //        `SVTEST ($sformatf("SPI status - check with other commands"))
    //            bit error;
    //            spi_read_status_seq status = new();
    //            spi_command_frame_seq frame = new();
    //            frame.add_command(status);
    //            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
    //            
    //            frame.start(sequencer);
    //            #1us;
    //            error = check_status(frame, {});
    //            `FAIL_UNLESS_EQUAL(error, 1'b0)
    //            `FAIL_UNLESS_EQUAL(get_errors(), 0)
    //        `SVTEST_END
    
    //FIXME: add tests with different CSB handlers! better: do all tests with different handlers
    
    
    //FIXME: add test
    //		`SVTEST ($sformatf("Interrupt read -> check next transfer and output of status word"))
    //			`FAIL_IF(1)
    //		`SVTEST_END
    
    //		for (time csn_time = 1ns; csn_time<100ns; csn_time+=1ns) begin
    //			_top_config._spi_config.sck_to_csn = csn_time;
    //			for (int i = 0; i<25; i++) begin
    //				spi_seq	seq;
    //				`SVTEST ($sformatf("%2d: Check written buffer with different timings", i, csn_time))
    //					seq = spi_test_seq::create_test_seq(sequencer, 20);
    //					seq.start(sequencer);
    //					#10us;
    //					`FAIL_UNLESS_EQUAL(get_errors(), 0)
    //					`FAIL_UNLESS_GREATER(_top_config._buffer_comparator.m_matches, 0, d)
    //				`SVTEST_END
    //			end
    //		end
    
    //FIXME: test "Abbrechen" Lesen und dann neues Kommando schicken --> FIFO Daten würden wohl noch geschickt werden
    
    /*FIXME:CRM/PDCM Leseszenarien:
     * - normal mit CRC
     * - mehrfach hintereinander + danach erst CRC
     * - verlängert (also mit 0x3/4000 aufgefüllt) mit CRC
     * - verkürzt mit CRC
     * - alles nochmal aber mit anderem Kommando danach und dann erst CRC
     * 
     */
    
    /*###   PDCM   ######################################################*/
    begin : pdcm_tests
        `SVTEST ($sformatf("PDCM read"))
            tdma_scheme_pdcm_denso scheme = new();
            spi_read_pdcm_frame_seq expected_pdcm_read;
            spi_command_frame_seq frame = new();
            spi_read_pdcm_frame_seq read_pdcm = new();
            int data_errors = 0;
            
            write_scheme_to_buffer('{0,1}, scheme);
            write_data_to_pdcm_buffer('{0,1}, scheme, expected_pdcm_read);
            for (int i = 0; i < DSI_CHANNELS; i++) begin
                _top_config._tdma_scheme_upload_listener.schemes[i] = scheme;
            end
            
            #1us;
            void'(read_pdcm.randomize() with {channel_bits == 2'b11;});
            frame.add_command(read_pdcm);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            for (int i = 2; i < frame.data_out.size()-2; i++) begin
                if (frame.data_out[i] != expected_pdcm_read.data_out[i]) begin
                    $error("Output data is not expected for word %1d! Got 0x%04h but expected 0x%04h", i, frame.data_out[i], expected_pdcm_read.data_out[i]);
                    data_errors++;
                end
            end
            `FAIL_UNLESS_EQUAL(data_errors, 0)
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        for (int read_channels = 0; read_channels < (1<<DSI_CHANNELS); read_channels++) begin
            for (int no_tdma_channels = 0; no_tdma_channels < (1<<DSI_CHANNELS); no_tdma_channels++) begin
                for (int no_data_channels=0; no_data_channels < (1<<DSI_CHANNELS); no_data_channels++) begin
                    `SVTEST ($sformatf("PDCM read of channel %2b - no TDMA on channel %2b, no DATA on channels %2b", read_channels, no_tdma_channels ,no_data_channels))
                    tdma_scheme_pdcm_denso scheme = new();
                    spi_command_frame_seq frame = new();
                    spi_read_pdcm_frame_seq   read_pdcm = new();
                    spi_status.no_tdma_scheme_defined = no_tdma_channels;
                    foreach (scheme.packets[i]) begin
                        scheme.packets[i].packet.crc_correct.rand_mode(1);
                        void'(scheme.packets[i].packet.randomize() with {data.size() == scheme.packets[i].symbol_count; crc_correct == 1'b1;});
                    end
                    for (int i = 0; i < DSI_CHANNELS; i++) begin
                        bit is_valid = ~no_tdma_channels[i];
                        tdma_scheme_pdcm_denso scheme = new();
                        _top_config._tdma_scheme_upload_listener.schemes[i] = scheme;
                        _top_config._tdma_scheme_upload_listener.schemes[i].valid = is_valid;
                        _top_config._tdma_scheme_upload_listener.schemes[i].pdcm_period = 800+i;
                        if (is_valid == 1'b1)
                            write_scheme_to_buffer('{i}, scheme);
                    end
                    
                    #1us;
                    void'(read_pdcm.randomize() with {channel_bits == read_channels[DSI_CHANNELS-1:0];});
                    frame.add_command(read_pdcm);
                    spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
                    frame.start(sequencer);
                    #1us;
                    //FIXME: add checks for data 0!
                    //            read_pdcm.expect_spi_data_packet(0,packet);
                    `FAIL_UNLESS_EQUAL(get_errors(), 0)
                    `SVTEST_END
                end
            end
        end
        
        for (int channels = 0; channels < 1<<DSI_CHANNELS; channels++) begin
            `SVTEST ($sformatf("PDCM read - no DATA on channels %2b",channels))
            tdma_scheme_pdcm_denso scheme = new();
            spi_command_frame_seq frame = new();
            spi_read_pdcm_frame_seq   read_pdcm = new();
            write_scheme_to_buffer('{0,1}, scheme);
            foreach (scheme.packets[i]) begin
                scheme.packets[i].packet.crc_correct.rand_mode(1);
                void'(scheme.packets[i].packet.randomize() with {data.size() == scheme.packets[i].symbol_count; crc_correct == 1'b1;});
            end
            for (int i = 0; i < DSI_CHANNELS; i++) begin
                _top_config._tdma_scheme_upload_listener.schemes[i] = scheme;
            end
            
            #1us;
            void'(read_pdcm.randomize() with {channel_bits == channels[1:0];});
            frame.add_command(read_pdcm);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            //FIXME: add checks for data 0!
            //            read_pdcm.expect_spi_data_packet(0,packet);
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
            `SVTEST_END
        end
        
        
        
        `SVTEST ($sformatf("PDCM read 2 frames"))
            tdma_scheme_pdcm_denso scheme = new();
            spi_read_pdcm_frame_seq expected_pdcm_read;
            spi_command_frame_seq frame = new();
            spi_read_pdcm_frame_seq read_pdcm = new();
            
            write_scheme_to_buffer('{0,1}, scheme);
            write_data_to_pdcm_buffer('{0,1}, scheme, expected_pdcm_read);
            write_data_to_pdcm_buffer('{0,1}, scheme, expected_pdcm_read);
            for (int i = 0; i < DSI_CHANNELS; i++) begin
                _top_config._tdma_scheme_upload_listener.schemes[i] = scheme;
            end
            
            #1us;
            void'(read_pdcm.randomize() with {channel_bits == 2'b11;});
            frame.add_command(read_pdcm);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame));
            frame.start(sequencer);
            #1us;
            frame.start(sequencer);
            #1us;
            
            //FIXME: check
            //            read_pdcm.expect_spi_data_packet(0,packet);
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
    end
    
    /*###   RESET   ######################################################*/
    begin
        `SVTEST ($sformatf("RESET command check with 0xffff ffff ffff fffF"))
            logic   reset_received = i_spi.reset_received;
            spi_any_command_seq any_seq = new();
            spi_command_frame_seq frame = new();
            
            repeat(4)
                any_seq.command_words.push_back(16'hffff);
            frame.add_command(any_seq);
            
            _top_config._command_buffer_creator.reset_buffer();
            frame.start(sequencer);
            #2us;
            `FAIL_UNLESS_EQUAL(i_spi.reset_received, ~reset_received)
            //FIXME: add checks
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("RESET command check with 0xffff ffff ffff fffE"))
            logic   reset_received = i_spi.reset_received;
            spi_any_command_seq any_seq = new();
            spi_command_frame_seq frame = new();
            
            repeat(3)
                any_seq.command_words.push_back(16'hffff);
            any_seq.command_words.push_back(16'hfffe);
            frame.add_command(any_seq);
            
            _top_config._command_buffer_creator.reset_buffer();
            frame.start(sequencer);
            #2us;
            `FAIL_UNLESS_EQUAL(i_spi.reset_received, ~reset_received)
            //FIXME: add checks
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("RESET command check with 0xffff ffff ffff fffC"))
            logic   reset_received = i_spi.reset_received;
            spi_any_command_seq any_seq = new();
            spi_command_frame_seq frame = new();
            
            repeat(3)
                any_seq.command_words.push_back(16'hffff);
            any_seq.command_words.push_back(16'hfffc);
            frame.add_command(any_seq);
            
            frame.start(sequencer);
            #2us;
            `FAIL_UNLESS_EQUAL(i_spi.reset_received, reset_received)
            //FIXME: add checks
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
        `SVTEST ($sformatf("RESET command check with 0xffff ffff ffff fffD"))
            logic   reset_received = i_spi.reset_received;
            spi_any_command_seq any_seq = new();
            spi_command_frame_seq frame = new();
            
            repeat(3)
                any_seq.command_words.push_back(16'hffff);
            any_seq.command_words.push_back(16'hfffd);
            
            frame.add_command(any_seq);
            frame.start(sequencer);
            #2us;
            `FAIL_UNLESS_EQUAL(i_spi.reset_received, reset_received)
            //FIXME: add checks
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
            
        `SVTEST ($sformatf("RESET command check"))
            logic   reset_received = i_spi.reset_received;
            spi_reset_seq reset;
            spi_command_frame_seq frame = new();
            reset = spi_seq_factory#(spi_reset_seq)::create_seq();
            frame.add_command(reset);
            frame.add_command(spi_seq_factory#(spi_read_status_seq)::create_seq());
            _top_config._command_buffer_creator.reset_buffer();
            frame.start(sequencer);
            #2us;
            `FAIL_UNLESS_EQUAL(i_spi.reset_received, ~reset_received)
            //FIXME: add checks
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
            
        `SVTEST ($sformatf("RESET command - CRC output reset check"))
            logic   reset_received = i_spi.reset_received;
            spi_reset_seq reset;
            spi_crm_seq crm;
            spi_command_frame_seq frame = new();
            spi_command_frame_seq frame2 = new();
            reset = spi_seq_factory#(spi_reset_seq)::create_seq();
            crm = spi_seq_factory#(spi_crm_seq)::create_seq();
            crm.channel_bits = '1;
            frame.add_command(reset);
            frame2.add_command(spi_seq_factory#(spi_read_status_seq)::create_seq());
            frame2.add_command(crm);
            spi_test_seq::append_crc_command_with(.crc_correct(1'b1), .frame(frame2));
            
            
            frame.start(sequencer);
            _top_config._command_buffer_creator.reset_buffer();
            #2us;
            frame2.start(sequencer);
            #2us;
            `FAIL_UNLESS_EQUAL(i_spi.reset_received, ~reset_received)
            `FAIL_UNLESS_EQUAL(get_errors(), 0)
        `SVTEST_END
        
    end
    
    //FIXME: check me again
    //      for (int bit_count = 1; bit_count <17; bit_count++) begin
    //          `SVTEST ($sformatf("Check transfer of less bits with %1d bits in last word", bit_count))
    //              spi_command_frame_seq frame = new();
    //              begin
    //                  spi_write_master_register_seq seq = new();
    //                  seq.randomize() with {address == ADDR_INTERRUPT_IRQ_MASK[11:0]; data == 16'h0000;};
    //                  frame.add_command(seq);
    //              end
    //              frame.crc_bit_count = bit_count;
    //              frame.start(sequencer);
    //              #1us;
    //              frame = spi_test_seq::create_register_read(sequencer, 1);
    //              frame.start(sequencer);
    //              if (bit_count == 16) check_status(frame, {});
    //              else check_status(frame, {SPICRC, SCI});
    //              #1us;
    //              frame = spi_test_seq::create_register_read(sequencer, 1);
    //              frame.start(sequencer);
    //              check_status(frame, {});
    //              #1us;
    //              `FAIL_UNLESS_EQUAL(get_errors(), 0)
    //          `SVTEST_END
    //      end
    
    //FIXME: add test with more or less bits in a word (alignment error)
    //FIXME: add test cases:
    //FIXME: read no channel bits set
    //FIXME: read without TDMA scheme an then while reading TDMA scheme becomes active
    //FIXME: abort reading PDCM of longest possible packet!
    //FIXME: abort reading PDCM at first packet with long data in buffers!
    
    enable_clk = 1'b0;
    `SVUNIT_TESTS_END
    
endmodule
