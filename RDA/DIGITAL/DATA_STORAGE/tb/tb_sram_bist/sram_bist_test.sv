`include "svunit_defines.svh"
`include "clk_rst_define.sv"

module sram_bist_test import project_pkg::*; ();

    localparam string path_to_RAM = "testrunner.ts.ut.dut.utils_sram_with_bist_inst.utils_sram_scan_shell_inst.sync_sram_inst.sram_inst.mem";

    `include "uvm_macros.svh"

    import svunit_pkg::svunit_testcase;
    import svunit_uvm_mock_pkg::*;
    import crc_calculation_pkg::spi_crc_ccitt_16;
    import addresses_pkg::*;
    import test_addresses_pkg::*;
    import common_test_pkg::*;
    import uvm_pkg::*;
    import unit_test_pkg::*;
    import elip_bus_pkg::*;
    import bist_pkg::*;

    string name = "sram_bist_test";
    svunit_testcase svunit_ut;

    elip_bus_sequencer_t	jtag_sequencer;
    elip_bus_sequencer_t	elip_sequencer;

    top_config				_top_config;

    `clk_def(27777ps)

    elip_if #(.addr_width(16), .data_width(16)) elip_registers();
    elip_full_if elip_ram();
    jtag_bus_if #(8, 16) jtag_bus ();

    elip_bus_if elip_bus_jtag();
    elip_bus_if elip_bus_ram();

    jtag_dr_for_registers_t	jtag_dr_read;

    SRAM_BIST_STAT_t bist_status;
    SRAM_BIST_CTRL_t bist_control;

    initial begin
        _top_config = new("_top_config");
        uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
        uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);

        _top_config._elip_jtag_config.vif	= elip_bus_jtag;
        _top_config._elip_ram_config.vif	= elip_bus_ram;
        //		foo = 1'b0; // just for debugging VERDI
        
        bist_control.BITWISE = 1'b0;
        bist_control.EN      = 1'b0;
        bist_control.FOUR_6N = 1'b0;
        
        run_test();
    end

    //===================================
    // This is the UUT that we're
    // running the Unit Tests on
    //===================================
    ecc_error_if ecc_error ();
    ram_wrapper_ecc_with_bist dut (
            .clk_rst      (clk_rst.slave     ),
            .elip         (elip_ram.slave    ),
            .jtag_bus     (jtag_bus.slave    ),
            .i_scan_mode  (1'b0        ),
            .o_jtag_dr    (jtag_dr_read),
            .ecc_error    (ecc_error.master   )
        );

    assign	elip_ram.addr = elip_bus_ram.address;
    assign	elip_ram.rd = elip_bus_ram.read;
    assign	elip_ram.wr = elip_bus_ram.write;
    assign	elip_ram.data_write = elip_bus_ram.data_write;
    assign	elip_bus_ram.data_read = elip_ram.data_read;
    assign	elip_bus_ram.ready = elip_ram.ready;
    assign	elip_bus_ram.clk = clk_rst.clk;
    assign	elip_bus_ram.rstn = clk_rst.rstn;

    assign	jtag_bus.addr = elip_bus_jtag.address[7:0];
    assign	jtag_bus.rd = elip_bus_jtag.read;
    assign	jtag_bus.wr = elip_bus_jtag.write;
    assign	jtag_bus.data_write = elip_bus_jtag.data_write;
    assign  jtag_bus.clk = elip_bus_jtag.clk;
    assign  jtag_bus.rstn = clk_rst.rstn;
    assign	elip_bus_jtag.data_read = jtag_dr_read;
    assign	elip_bus_jtag.ready = 1'b1;
    assign	elip_bus_jtag.clk = clk_rst.clk;
    assign	elip_bus_jtag.rstn = clk_rst.rstn;

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
        set_por();
        _wait(15);
    endtask

    //===================================
    // Here we deconstruct anything we
    // need after running the Unit Tests
    //===================================
    task teardown();
        svunit_ut.teardown();
        /* Place Teardown Code Here */
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

    function automatic int get_errors();
        int errors = 0;
        if (!uvm_report_mock::verify_complete())
            errors++;
        return errors;
    endfunction

    
    localparam time RAM_BIST_TIME = 5ms;

    task _wait(input int wait_cycles=2);
        wait_for_n_clocks(wait_cycles);
    endtask

    /*###   JTAG tasks   ######################################################*/
    task automatic write_to_sram_bist_control_register(SRAM_BIST_CTRL_t bist_control);
        elip_write_seq	jtag = new();
        jtag.address = test_addresses_pkg::ADDR_TEST_SRAM_SRAM_BIST_CTRL;
        jtag.data = {4'b0, bist_control};
        jtag.start(jtag_sequencer);
    endtask

    task automatic write_to_sram_bist_status_register(SRAM_BIST_STAT_t bist_status);
        elip_write_seq	jtag = new();
        jtag.address = test_addresses_pkg::ADDR_TEST_SRAM_SRAM_BIST_STAT;
        jtag.data = {14'b0, bist_status};
        jtag.start(jtag_sequencer);
    endtask

    task automatic get_bist_status();
        elip_read_seq	elip_seq = new();
        elip_seq.address = test_addresses_pkg::ADDR_TEST_SRAM_SRAM_BIST_STAT;
        elip_seq.start(jtag_sequencer);
        bist_status = SRAM_BIST_STAT_t'(elip_seq.data);
        #10us;
    endtask

    /*###   JTAG tasks   ######################################################*/
    task automatic read_ram(input shortint address, output shortint data);
        elip_read_seq	ram_seq = new();
        ram_seq.address = address;
        ram_seq.start(elip_sequencer);
        data = ram_seq.data[15:0];
    endtask
    /*###   Set sram bist register to 0   ######################################################*/
    task automatic reset_tb_sram_bist_registers();
        bist_control.BITWISE = 1'b0;
        bist_control.EN      = 1'b0;
        bist_control.FOUR_6N = 1'b0;
    endtask
    
/*###   TEST CASES   ######################################################*/
`SVUNIT_TESTS_BEGIN
     enable_clk = 1'b1;
     #10us;
     jtag_sequencer = _top_config._elip_jtag_agent.m_sequencer;
     elip_sequencer = _top_config._elip_ram_agent.m_sequencer;

    `SVTEST ($sformatf("check initial status"))
        get_bist_status();
        `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_INIT)
    `SVTEST_END

    `SVTEST ($sformatf("check status running"))
        reset_tb_sram_bist_registers();
        bist_control.EN = 1'b1;
        write_to_sram_bist_control_register(bist_control);
        #100us;
        get_bist_status();
        `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_BUSY)
    `SVTEST_END

    `SVTEST ($sformatf("check status pass"))
        reset_tb_sram_bist_registers();
        bist_control.EN = 1'b1;
        write_to_sram_bist_control_register(bist_control);
        #(RAM_BIST_TIME);
        get_bist_status();
        `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_PASS)
    `SVTEST_END

    `SVTEST ($sformatf("check status fail"))
        reset_tb_sram_bist_registers();
        `ifdef full_BIST
            for (int row = 0; row < 368; row++) begin
                for (int col = 0; col < 191; col++) begin
                    for (int value = 0; value < 2; value++) begin
                        string value_string = $sformatf("%1b", $urandom_range(1,0));
                        string path_to_RAMcell = $sformatf("%s[%1d][%1d]", path_to_RAM, row, col);
                        $hdl_xmr_force(path_to_RAMcell,value_string, , , ,0);
                        bist_control.EN = 1'b1;
                        write_to_sram_bist_control_register(bist_control);
                        #(RAM_BIST_TIME);
                        get_bist_status();
                        `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_FAIL)
                        $hdl_xmr_release(path_to_RAMcell, 0);
                        reset_tb_sram_bist_registers();
                        write_to_sram_bist_control_register(bist_control);
                    end
                end
            end
        `else
            repeat(20) begin
                int row = $urandom_range(63,0);
                int col = $urandom_range(255,0);
                string value_string = $sformatf("%1b", $urandom_range(1,0));
                string path_to_RAMcell = $sformatf("%s[%1d][%1d]", path_to_RAM, row, col);
                $hdl_xmr_force(path_to_RAMcell,value_string, , , ,0);
                bist_control.EN = 1'b1;
                write_to_sram_bist_control_register(bist_control);
                #(RAM_BIST_TIME);
                get_bist_status();
                `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_FAIL)
                $hdl_xmr_release(path_to_RAMcell, 0);
                reset_tb_sram_bist_registers();
                write_to_sram_bist_control_register(bist_control);
            end
    `endif

    `SVTEST_END

    `SVTEST ($sformatf("check status pass again"))
        time start = '0;
        time duration = '0;

        reset_tb_sram_bist_registers();
        bist_control.EN = 1'b1;
        write_to_sram_bist_control_register(bist_control);
        start = $time;
        #2us;
        get_bist_status();
        while (bist_status.STATUS == BIST_BUSY) begin
            get_bist_status();
        end
        duration = $time - start;
        $display($sformatf("Normal bist test needed %0f ms", duration/1.0ms ));
        get_bist_status();
        `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_PASS)
        
    `SVTEST_END

    `SVTEST ($sformatf("check writing to status will not change it"))
        reset_tb_sram_bist_registers();
        bist_control.EN = 1'b1;
        write_to_sram_bist_control_register(bist_control);
        #(RAM_BIST_TIME);
        for (int i=0; i<4; i++) begin
            bist_status.STATUS = i;
            write_to_sram_bist_status_register(bist_status);
            get_bist_status();
            `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_PASS)
        end
    `SVTEST_END

    `SVTEST ($sformatf("check bist status pass with additional bitwise check"))
        time start = '0;	
        time duration = '0;
        reset_tb_sram_bist_registers();
        
        bist_control.EN = 1'b1;
        bist_control.BITWISE = 1'b1;
        write_to_sram_bist_control_register(bist_control);
        start = $time;
        #2us;
        get_bist_status();
        while (bist_status.STATUS == BIST_BUSY) begin
            get_bist_status();
        end
        duration = $time - start;
        $display($sformatf("Bist incl. addidtional bitwise test needed %0f ms", duration/1.0ms ));
        `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_PASS)
    `SVTEST_END

    `SVTEST ($sformatf("check bist status pass with additional FOUR_6N check"))
        time start = '0;
        time duration = '0;

        reset_tb_sram_bist_registers();
        bist_control.EN = 1'b1;
        bist_control.FOUR_6N = 1'b1;
        start = $time;
        write_to_sram_bist_control_register(bist_control);
        #2us;
        get_bist_status();
        while (bist_status.STATUS == BIST_BUSY) begin
            get_bist_status();
        end
        duration = $time - start;
        $display($sformatf("Bist incl. addidtional FOUR_6N test needed %0f ms", duration/1.0ms ));
        `FAIL_UNLESS_EQUAL(bist_status.STATUS, BIST_PASS)
    `SVTEST_END


        enable_clk = 1'b0;
`SVUNIT_TESTS_END
endmodule
