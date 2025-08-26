//        `define NO_DM_TEST
//        `define NO_CRM_TEST
//        `define NO_TDMA_TESTS
//        `define NO_PDCM_TEST

`include "svunit_defines.svh"


class packet_number_generator;
    rand int unsigned packets[];
    int unsigned max_number_of_symbols;
    rand int unsigned number_of_symbols;
    
    constraint co_symbols       {number_of_symbols == max_number_of_symbols;}
    constraint co_symbols_sum   { packets.sum < number_of_symbols;}
    constraint co_symbol_counts { foreach(packets[i]) {
                packets[i] <= 16'hffff;
                packets[i] > 3;
                packets[i] < 256;
            }
    }
    
    static function packet_number_generator get_instance(int unsigned packets, int unsigned max_number_of_symbols = 145*4);
        packet_number_generator new_generator = new(packets, max_number_of_symbols);
        void'(new_generator.randomize());
        return new_generator;
    endfunction
    
    function void post_randomize();
        packets.shuffle();
    endfunction
    
    function new(int unsigned number_of_packets, int unsigned max_number_of_symbols);
        packets = new[number_of_packets];
        this.max_number_of_symbols = max_number_of_symbols;
    endfunction
    
endclass

module dsi3_block_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import dsi3_slave_pkg::*;
	import uvm_pkg::*;
	import unit_test_pkg::*;
	import common_env_pkg::*;
	import spi_pkg::*;
	import dsi3_pkg::*;
	import elip_bus_pkg::*;
	import tdma_pkg::*;
    import buffer_if_pkg::*;
    import top_pkg::*;

	string name = "dsi3_core_test";
	svunit_testcase svunit_ut;
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
    
	unit_test_top_config	_top_config;
	dsi3_slave_if			slave_if();
	
	jtag_bus_if #(.addr_width  (JTAG_IR_WIDTH ), .data_width  (JTAG_DR_WIDTH )) jtag_bus ();
	tmr_dsi_if 				tmr_dsi ();
	tmr_out_dsi_if			tmr_out_dsi ();
	
	frame_facade			_frame_facade;
	
	dsi3_start_request_if	request();
	ecc_error_if #(1) 		buf_ecc_error ();
	ecc_error_if #(1) 		dsi_cmd_ecc_error ();
	ecc_error_if #(1) 		dsi_data_ecc_error ();
	ecc_error_if #(1) 		dsi_data_ecc_error_tdma ();
	
	`clk_def(27777ps)
	`tick_gen
	
	/*###   interface definitions   ######################################################*/
	buffer_writer_if command_writer ();
	buffer_reader_if command_reader ();
	pdcm_buffer_writer_if pdcm_data_writer	();
	buffer_writer_if crm_data_writer	();
	
	dsi3_io_if dsi3_io ();
	dsi3_common_config_if common_config ();
	timebase_info_if time_base ();
	
	elip_full_if elip_command_buffer ();
	elip_full_if elip_data_buffer ();
	elip_full_if elip_tdma ();
	elip_if #(.addr_width(16), .data_width(16)) elip_registers();
	
	elip_bus_if		elip_bus_command_buffer();
	elip_bus_if		elip_bus_tdma_buffer();
	elip_bus_if		elip_bus_registers();
    
    elip_bus_sequencer_t    elip_sequencer;
	
	synchronization_if	sync();
	
	parameter	shortint	BASE_ADDR_TDMA = 16'h2000;
	
	/*###   timebase   ######################################################*/
	initial begin
		time_base.base_time = '0;
		forever begin
			@(posedge tick_1us);
			if (tick_1us == 1'b1)
				time_base.base_time+=16'd1;
		end
	end
	assign	time_base.tick_1us = tick_1us;
	assign	time_base.tick_1ms = tick_1ms;
	
	/*###      ######################################################*/
	
	/*###   DSI3 block instance   ######################################################*/
	logic	i_transceiver_enable;
	logic	interrupt, transmit_pending;
	data_t	o_elip_register_read;
	logic	clear_dsi_command_queue, clear_dsi_crm_data_buffer, clear_dsi_pdcm_data_buffer;
	logic	tmr_dig_prevent_deactivation, hard_ware_error;
	shortint pdcm_period;
	logic	no_tdma_scheme_defined;
	logic	busy;
    data_t  tdma_frame_word_count;
    int     rx_dac;
    
	assign	sync.fire = 1'b0;
	assign	sync.armed = 1'b0;
		
	assign	jtag_bus.rstn = 1'b0;
	
	assign	request.tick_pdcm = request.request;
	assign	request.tick_transmit = request.request;
    
	
	initial begin
		request.pdcm_period_running = 1'b0;
		request.pdcm_receive_timeout = 1'b0;
	end
	
	typedef enum {FIRST_PACKET=0, LAST_PACKET=14, RANDOM_PACKET} packet_position_e;
	
	function automatic int get_packet_position(packet_position_e position, int packets);
		case (position)
			FIRST_PACKET: return 0;
			LAST_PACKET: return packets-1;
			default: begin
				if (packets > 2)
					return $urandom_range(packets-1, FIRST_PACKET+1);
				return packets-1;
			end
		endcase
	endfunction
	
	always@(posedge request.request) begin
		fork
			begin
				if (request.mode == MODE_PDCM) begin
					wait_for_n_clocks(1);
					request.pdcm_period_running = 1'b1;
					#((pdcm_period-10)*1us);
					request.pdcm_receive_timeout = 1'b1;
					wait_for_n_clocks(1);
					request.pdcm_receive_timeout = 1'b0;
					#10us;
					request.pdcm_period_running = 1'b0;
				end
			end
		join_none
	end
		
	dsi3_block #(
		.BASE_ADDR                          (BASE_ADDR_DSI[0]                  ), 
		.BASE_ADDR_TEST                     (BASE_ADDR_TEST_DSI[0]             ), 
		.BASE_ADDR_TRIMMING                 (BASE_ADDR_TEST_DSI[0]             ), 
		.ADDR_WIDTH                         (16                                ),
		.BASE_ADDR_TDMA                     (BASE_ADDR_TDMA                    ),
		.CHANNEL                            (0                                 )
	) i_dsi3_block (
		.clk_rst                            (clk_rst.slave                     ), 
		.command_reader                     (command_reader.master             ), 
		.pdcm_data_writer                   (pdcm_data_writer.master           ), 
		.crm_data_writer                    (crm_data_writer.master            ), 
		.dsi3_io                            (dsi3_io.dsi3_block                ), 
		.common_config                      (common_config.dsi3_block          ), 
		.time_base                          (time_base.slave                   ), 
		.request                            (request.master                    ),
		.sync                               (sync.master                       ),
		.tmr_dsi                            (tmr_dsi.master                    ),
		.tmr_out_dsi                        (tmr_out_dsi.master                ),
		.jtag_bus                           (jtag_bus.slave                    ), 
		.o_jtag_dr                          (                                  ), 
		.elip_registers                     (elip_registers.slave              ), 
		.o_elip_register_read               (o_elip_register_read              ), 
		.i_transceiver_enable               (i_transceiver_enable              ), 
		.i_stop_transmission                (clear_dsi_command_queue           ),
		.i_clear_crm_data_buffer            (clear_dsi_crm_data_buffer         ), //TODO: test me!
		.i_clear_pdcm_data_buffer           (clear_dsi_pdcm_data_buffer        ), //TODO: test me!
        .i_invalidate_tdma_scheme           (1'b0                              ), //TODO: test me!
		.o_interrupt                        (interrupt                         ), //TODO: test me! 
		.o_hard_ware_error                  (hard_ware_error                   ), //TODO: test me!
		.o_tmr_dig_prevent_deactivation     (tmr_dig_prevent_deactivation      ), //TODO: test me!
		.o_transmit_pending                 (transmit_pending                  ),
		.ecc_error_cmd                      (dsi_cmd_ecc_error.master          ), //TODO: test me!
		.ecc_error_data                     (dsi_data_ecc_error.master         ), //TODO: test me!
		.ecc_error_tdma                     (dsi_data_ecc_error_tdma.master    ), //TODO: test me!
		.i_sync_error                       (1'b0                              ), //TODO: test me!
		.o_hard_ware_error_irq              (                                  ), //TODO: test me!
		.o_hw_fail                          (                                  ), //TODO: test me!
		.o_clear_command_queue              (                                  ), //TODO: test me!
		.o_busy                             (busy                              ),
		.i_clear_and_invalidate_crm_data_buffer (1'b0                          ), //TODO: test me!
		.i_clear_and_invalidate_pdcm_data_buffer (1'b0                         ), //TODO: test me!
		.elip_tdma							(elip_tdma.master                  ),
		.o_no_tdma_scheme_defined			(no_tdma_scheme_defined            ),
        .o_tdma_frame_word_count            (tdma_frame_word_count             ),
        .i_set_command_error(1'b0)
    ); //TODO: test me!
	
	interface_converter_elip_full_2_elip_bus i_interface_converter_command_buffer (
			.clk_rst    (clk_rst.slave             ),
			.elip_full  (elip_command_buffer.slave ), 
			.elip_bus   (elip_bus_command_buffer  ));
	
	interface_converter_elip_full_2_elip_bus i_interface_converter_tdma_buffer (
			.clk_rst    (clk_rst.slave             ),
			.elip_full  (elip_tdma.slave ), 
			.elip_bus   (elip_bus_tdma_buffer  ));
	
	interface_converter_elip_bus_2_elip #(.data_width  (16 )) i_interface_converter_registers (
		.clk_rst     (clk_rst.slave    ), 
		.elip_bus    (elip_bus_registers   ), 
		.elip        (elip_registers.master       ), 
		.i_data_out  (o_elip_register_read ));
	
	ram_model #(
		.OFFSET(BASE_ADDR_DSI_CMD_BUF[0]),
		.RAM_SIZE  ('h100)
	) i_command_buffer_model (
		.clk_rst   (clk_rst.slave  ), 
		.elip      (elip_command_buffer.slave     )
	);
	
	ram_model #(
		.OFFSET(BASE_ADDR_TDMA),
		.RAM_SIZE  ('h40)
	) i_tdma_buffer_model (
		.clk_rst   (clk_rst.slave  ), 
		.elip      (elip_tdma.slave     )
	);
	
	buffer #(
			.BASE_ADDR                  (BASE_ADDR_DSI_CMD_STAT[0]       ),
			.ADDR_WIDTH                 (16                              ), 
			.BUFFER_OFFSET_ADDRESS      (BASE_ADDR_DSI_CMD_BUF[0]        ), 
			.BUFFER_SIZE                (SIZE_DSI_CMD_BUF                ), 
			.PRIORITY_READ              (1'b0             )
		) i_dsi3_command_buffer (
			.clk_rst                    (clk_rst.slave                   ), 
			.reader                     (command_reader.slave            ), 
			.writer                     (command_writer.slave            ), 
			.elip                       (elip_command_buffer.master      ), 
			.elip_registers             (elip_registers.slave            ), 
			.o_elip_registers_data_out  (                                ),
			.o_data_available           (                                ),
			.ecc_error                  (buf_ecc_error.master            ));
			
	
	/*###   start simulation   ######################################################*/
	initial begin
		_top_config = new("_top_config");
		
		uvm_config_db #(unit_test_top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
		uvm_config_db #(unit_test_top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
		
		_top_config._dsi3_slave_config.vif		= slave_if;
		_top_config._dsi3_master_config.vif		= slave_if;
		_top_config._writer_config.vif			= command_writer;
		_top_config._writer_config.vif_clk_rst	= clk_rst;
		_top_config._reader_config.vif			= command_reader;
		_top_config._reader_config.vif_clk_rst	= clk_rst;
		_top_config._elip_command_config.vif	= elip_bus_command_buffer;
		_top_config._elip_register_config.vif	= elip_bus_registers;
		_top_config._elip_tdma_config.vif		= elip_bus_tdma_buffer;
		
		_top_config._pdcm_data_writer_config.vif		= pdcm_data_writer;
		_top_config._pdcm_data_writer_config.vif_clk_rst= clk_rst;
		_top_config._crm_data_writer_config.vif			= crm_data_writer;
		_top_config._crm_data_writer_config.vif_clk_rst	= clk_rst;
		
		run_test();
	end
	
	initial begin
		i_transceiver_enable = 1'b0;
		dsi3_io.rx = '0;
		dsi3_io.uv = 1'b0;
		dsi3_io.ov = 1'b0;
		time_base.clkref_ok = 1'b1;
	end
	
	always@(slave_if.cable.Current) begin
		dsi3_io.rx[0] = (slave_if.cable.Current > 0) ? 1'b1 : 1'b0;
		dsi3_io.rx[1] = (slave_if.cable.Current > 1) ? 1'b1 : 1'b0;
	end
	assign	slave_if.cable.Voltage = dsi3_io.tx;
    
    always_comb begin
        if (int'(dsi3_io.rx_idac) >= rx_dac)
            dsi3_io.i_q = 1'b0;
        else
            dsi3_io.i_q = 1'b1;
    end
	
	function automatic int get_errors();
		int errors = 0;
		errors += _top_config._check_elip.get_error_count();
		errors += _top_config._check_elip_tdma.get_error_count();
		errors += _top_config._check_receive_pdcm.get_error_count();
		errors += _top_config._check_receive_crm.get_error_count();
		errors += _top_config._check_transmit.get_error_count();
		if(!uvm_report_mock::verify_complete())
			errors++;
		return errors;
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
		
		if (_frame_facade == null)
			_frame_facade = _top_config._frame_facade;
		slave_if.cable.Current = 0;
		uvm_report_mock::setup();
		common_config.bit_time = BITTIME_8US;
		common_config.chip_time = 'd1;
		common_config.sync_pdcm = 1'b0;
		common_config.crc_enable = 1'b0;
		common_config.timeout_crm = 450;
		common_config.timeout_crm_nr = 320;
		clear_dsi_command_queue = 1'b0;
		clear_dsi_crm_data_buffer = 1'b0;
		clear_dsi_pdcm_data_buffer = 1'b0;
        rx_dac = 1;
		set_por();
		#1us;
		update_master_config();
		_top_config._check_receive_pdcm.initialize();
		_top_config._check_receive_crm.initialize();
		_top_config._check_transmit.initialize();
		_top_config._check_elip.initialize();
		i_transceiver_enable = 1'b1;
		#10us;
	endtask

	//===================================
	// Here we deconstruct anything we 
	// need after running the Unit Tests
	//===================================
	task teardown();
		svunit_ut.teardown();
		
		i_transceiver_enable = 1'b0;
		slave_if.cable.Current = 0;
		#1us;
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
	
    function automatic void set_symbol_coding_error(tdma_scheme_pdcm scheme, int packet_index);
        foreach (scheme.packets[i]) begin
            scheme.packets[i].symbol_coding_error_injection = (i == packet_index) ? common_env_pkg::ALWAYS_ERROR : common_env_pkg::NEVER_ERROR; // inject SE
        end
    endfunction
    
	function automatic void update_master_config();
		dsi3_master_configuration_tr t = dsi3_master_configuration_tr::create_transaction();
		t.bit_time	= common_config.bit_time;
		t.chip_time = common_config.chip_time+2; 
		t.crc_en	= common_config.crc_enable; 
		t.sync_pdcm	= common_config.sync_pdcm; 
        t.crm_time  = common_config.timeout_crm;
        t.crm_time_nr = common_config.timeout_crm_nr;
        t.tx_shift_value = common_config.tx_shift;
		_top_config._check_transmit.set_configuration(t);
		_top_config._check_receive_pdcm.set_configuration(t);
		_top_config._check_receive_crm.set_configuration(t);
		_top_config._dsi3_master_agent.m_config.configuration_subscriber.write(t);
		_top_config._dsi3_slave_agent.m_config.configuration_subscriber.write(t);
    endfunction
    
    function automatic void set_tdma_scheme(tdma_scheme_pdcm scheme);
        _top_config._check_receive_pdcm.scheme = scheme;
        pdcm_period = scheme.pdcm_period;
    endfunction
	
	function automatic tdma_scheme create_scheme_with_packet(tdma_scheme_packet packet);
		tdma_scheme scheme = new("scheme");
		dsi3_packet noise_data_packet = new();
		void'(noise_data_packet.randomize() with {data.size() == local::packet.symbol_count;});
		packet.packet = noise_data_packet;
		scheme.add_packet(packet);
		return scheme;
	endfunction
	
	function automatic tdma_scheme crm_slave_scheme(int start_time, int symbols, int chip_time=3);//, ref dsi3_packet packet);
		dsi3_packet next_packet = new();
		tdma_scheme scheme = tdma_scheme_crm::default_scheme(chip_time);
		void'(next_packet.randomize() with {data.size() == symbols;});
		scheme.packets[0].packet.data = next_packet.data;
		scheme.packets[0].earliest_start_time = start_time;
		scheme.packets[0].latest_start_time = start_time;
//		packet = next_packet;
		return scheme;
    endfunction
    
    function automatic void fill_scheme_with_data(tdma_scheme scheme);
        foreach(scheme.packets[i]) begin
            tdma_scheme_packet  scheme_packet = scheme.packets[i];
            dsi3_packet packet = scheme_packet.packet;
            void'(packet.randomize() with {data.size() == local::scheme_packet.symbol_count;});
        end
    endfunction
	
	function automatic tdma_scheme crm_slave_scheme_with_two_responses(int symbols, int chip_time=3);//, ref dsi3_packet packet);
		dsi3_packet next_packet = new();
		tdma_scheme scheme = tdma_scheme_crm::default_scheme(chip_time);
		void'(next_packet.randomize() with {data.size() == symbols;});
		scheme.packets[0].packet.data = next_packet.data;
		scheme.packets[0].earliest_start_time = 270;
		scheme.packets[0].latest_start_time = 270;
		scheme.add_packet(tdma_scheme_packet_crm::new_packet(370, 370, 8, 0.99, 1.01, NEVER_ERROR));
		void'(next_packet.randomize() with {data.size() == symbols;});
		scheme.packets[1].packet.data = next_packet.data;
		return scheme;
	endfunction
	
	function automatic tdma_scheme_pdcm create_valid_scheme(int packets=15);
		tdma_scheme_pdcm scheme;
		scheme =  new("pdcm_TDMA_scheme");
		scheme.pdcm_period = 150;
		scheme.chiptime = 3;
		for (int i = 0; i < packets; i++) begin
			scheme.add_packet(tdma_scheme_packet_crm::new_packet( 30+i*100,  70+i*100, 8));
			scheme.pdcm_period += 100;
		end
		return scheme;
	endfunction
	
	task automatic read_register(shortint address, output shortint data);
		elip_read_seq elip_seq = new();
		void'(elip_seq.randomize with {address == local::address; });
		elip_seq.start(_top_config._elip_register_agent.m_sequencer);
		data = elip_seq.data;
    endtask
    
    task automatic upload_scheme(tdma_scheme_pdcm scheme);
        _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
    endtask
    
    task automatic upload_denso_scheme();
        tdma_scheme_pdcm_denso denso_scheme = new();
        upload_scheme(denso_scheme);
    endtask
    
    task automatic send_slave_packet(dsi3_pdcm_packet packet);
        dsi3_slave_tr slave_tr = new();
        dsi3_slave_seq seq = new();
        dsi3_slave_sequencer_t sequencer = _top_config._dsi3_slave_agent.m_sequencer;
        void'(slave_tr.randomize() with {msg_type == dsi3_pkg::PDCM; data.size() == packet.data.size(); foreach(data[i]) data[i] == packet.data[i]; chips_per_symbol == 3; chiptime == 3; tolerance_int == 1000; symbol_coding_error_injection == NEVER_ERROR;});
        seq.packet = packet;
        seq.req = slave_tr;
        seq.start(sequencer);
    endtask
    
    function automatic int get_word_count_of_scheme(tdma_scheme_pdcm scheme);
        int words = 1;
        foreach(scheme.packets[i]) begin
            words++;
            words += scheme.packets[i].get_word_count_of_data();
        end
        return words;
    endfunction
	
    task automatic read_elip (input elip_addr_t address, output data_t data);
        elip_bus_seq    seq = new();
        elip_tr         tr = new();
        void'(tr.randomize with {write == 1'b0; address == local::address;});
        seq.req= tr;
        seq.start(elip_sequencer);
        data = seq.req.data_read;
    endtask
    
    task automatic write_elip(input elip_addr_t address, input data_t data);
        elip_bus_seq    seq = new();
        elip_tr         tr = new();
        void'(tr.randomize with {write == 1'b1; address == local::address; data_write == local::data;});
        seq.req= tr;
        seq.start(elip_sequencer);
        @(posedge clk_rst.clk);
    endtask
    
	dsi3_bit_time_e bit_time;
	dsi3_chip_time_e chip_time;
    int word_count;
	
	`SVUNIT_TESTS_BEGIN
	begin
		enable_clk = 1'b1;
		#1us;
        elip_sequencer   = _top_config._elip_register_agent.m_sequencer;
		
		`ifndef NO_DM_TEST
		//##########   Discovery Mode   ###################################################
		bit_time = BITTIME_8US;
		do begin
			chip_time = chip_time.first;
			do begin
				for (int slaves=0; slaves<17; slaves++) begin
					`SVTEST($sformatf("Discovery mode with %2d slaves, %s and %s", slaves, bit_time.name(), chip_time.name))
						spi_command_frame_seq new_frame = new();
						tdma_scheme dm_scheme = _top_config._dsi3_slave_agent.m_config.dm_scheme;
						spi_discovery_mode_seq	dm_seq = spi_seq_factory#(spi_discovery_mode_seq)::create_seq();
						dm_seq.channel_bits = 2'b01;
						new_frame.add_command(dm_seq);
						_top_config._dsi3_slave_agent.m_master_subscriber.reset_dm_pulse_count();
						_top_config._check_receive_crm.expect_no_crm_response();
						if(dm_scheme.packets.size < slaves) begin
							dm_scheme.add_packet(tdma_scheme_packet_dm::new_packet( 58,  70, 1));
						end
						foreach (dm_scheme.packets[i]) begin
							dm_scheme.packets[i].enable = (i < slaves) ? 1'b1 : 1'b0;
							dm_scheme.packets[i].set_tolerance_limits(1.0, 1.0);
							dm_scheme.packets[i].earliest_start_time = 58; // + 2*(1+(bit_time==BITTIME_UNUSED?0:bit_time));
							dm_scheme.packets[i].latest_start_time = 70;// - 2*(1+(bit_time==BITTIME_UNUSED?0:bit_time));
						end
						common_config.bit_time = bit_time;
						common_config.chip_time = chip_time;
						update_master_config();
						_frame_facade.start_this(new_frame);
						#(0.13ms*(slaves+1)*dsi3_pkg::get_bit_time_factor(bit_time));
						`FAIL_IF(get_errors() > 0)
						`FAIL_UNLESS_EQUAL(busy, 1'b0);
						begin
							DSI_STAT_t	stat;
							DSI_IRQ_STAT_t	irq;
							read_register(ADDR_DSI_0_DSI_STAT, stat);
							read_register(ADDR_DSI_0_DSI_IRQ_STAT, irq);
							if (slaves <16) begin
								`FAIL_UNLESS_EQUAL(stat.SLAVES, slaves)
								`FAIL_UNLESS_EQUAL(irq.DMOF, 1'b0)
							end
							else begin
								`FAIL_UNLESS_EQUAL(stat.SLAVES, 4'd15)
								`FAIL_UNLESS_EQUAL(irq.DMOF, 1'b1)
							end
						end
					`SVTEST_END
				end
				chip_time = chip_time.next();
			end while (chip_time != chip_time.first);
			bit_time = bit_time.next();
		end while (bit_time != bit_time.first);
		
		`SVTEST($sformatf("Discovery mode early responses and %2d slaves", 8))
			spi_command_frame_seq new_frame = new();
			tdma_scheme dm_scheme = tdma_scheme_dm::valid();
			spi_discovery_mode_seq	dm_seq = spi_seq_factory#(spi_discovery_mode_seq)::create_seq();
			_top_config._dsi3_slave_agent.m_config.dm_scheme = dm_scheme;
			dm_seq.channel_bits = 2'b01;
			new_frame.add_command(dm_seq);
			_top_config._dsi3_slave_agent.m_master_subscriber.reset_dm_pulse_count();
			_top_config._check_receive_crm.expect_no_crm_response();
			foreach (dm_scheme.packets[i]) begin
				dm_scheme.packets[i].enable = (i < 8) ? 1'b1 : 1'b0;
				dm_scheme.packets[i].set_tolerance_limits(0.97, 1.03);
			end
			dm_scheme.packets[5].earliest_start_time = 28;
			dm_scheme.packets[5].latest_start_time = 30;
			dm_scheme.packets[5].set_tolerance_limits(1.0, 1.0);
			_frame_facade.start_this(new_frame);
			repeat(3)
				void'(_top_config._check_transmit.transmissions.pop_back());
			#(0.2ms*(8+1));
			`FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(busy, 1'b0);
			begin
				DSI_STAT_t	stat;
				DSI_IRQ_STAT_t	irq;
				read_register(ADDR_DSI_0_DSI_STAT, stat);
				read_register(ADDR_DSI_0_DSI_IRQ_STAT, irq);
				`FAIL_UNLESS_EQUAL(stat.SLAVES, 5)
				`FAIL_UNLESS_EQUAL(irq.DMOF, 1'b0)
			end
		`SVTEST_END
		
		`SVTEST($sformatf("Discovery mode late responses and %2d slaves", 11))
			spi_command_frame_seq new_frame = new();
			tdma_scheme dm_scheme = tdma_scheme_dm::valid();
			spi_discovery_mode_seq	dm_seq = spi_seq_factory#(spi_discovery_mode_seq)::create_seq();
			_top_config._dsi3_slave_agent.m_config.dm_scheme = dm_scheme;
			dm_seq.channel_bits = 2'b01;
			new_frame.add_command(dm_seq);
			_top_config._dsi3_slave_agent.m_master_subscriber.reset_dm_pulse_count();
			_top_config._check_receive_crm.expect_no_crm_response();
			foreach (dm_scheme.packets[i]) begin
				dm_scheme.packets[i].enable = (i < 11) ? 1'b1 : 1'b0;
			end
			dm_scheme.packets[7].earliest_start_time = 88;
			dm_scheme.packets[7].latest_start_time = 90;
			dm_scheme.packets[7].set_tolerance_limits(1.0, 1.0);
			_frame_facade.start_this(new_frame);
			repeat(4)
				void'(_top_config._check_transmit.transmissions.pop_back());
			#(0.2ms*(11+1));
			`FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(busy, 1'b0);
			begin
				DSI_STAT_t	stat;
				DSI_IRQ_STAT_t	irq;
				read_register(ADDR_DSI_0_DSI_STAT, stat);
				read_register(ADDR_DSI_0_DSI_IRQ_STAT, irq);
				`FAIL_UNLESS_EQUAL(stat.SLAVES, 7)
				`FAIL_UNLESS_EQUAL(irq.DMOF, 1'b0)
			end
		`SVTEST_END
		
		//FIXME: check DM with all bit times
		`endif
		
		`ifndef NO_CRM_TEST
		//##########   CRM   ###################################################
		`SVTEST("CRM send")
            bit transmit_was_pending;
			_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(tdma_scheme_crm::valid());
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(.number_of_commands(1), .bc(1'b0)));
            `FAIL_UNLESS_EQUAL(transmit_pending, 1'b0)
            fork
                begin
                   #100us;
                   transmit_was_pending = transmit_pending;
                end
    			#0.5ms;
            join
            `FAIL_UNLESS_EQUAL(transmit_was_pending, 1'b1)
            `FAIL_UNLESS_EQUAL(transmit_pending, 1'b0)
			`FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(busy, 1'b0);
		`SVTEST_END
			
		`SVTEST("CRM send NR")
			_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(tdma_scheme_crm::valid());
			_top_config._check_receive_crm.expect_no_crm_response();
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(.number_of_commands(1), .bc(1'b1)));
			#0.275ms;
            `FAIL_UNLESS_EQUAL(busy, 1'b1);
            #0.085ms;
            `FAIL_UNLESS_EQUAL(busy, 1'b0);
			`FAIL_IF(get_errors() > 0)
		`SVTEST_END
		
		`SVTEST("CRM send with too early timeout")
			_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(tdma_scheme_crm::valid());
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(.number_of_commands(1), .bc(1'b0)));
			common_config.timeout_crm = 250;
			#0.5ms;
			`FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(busy, 1'b0);
		`SVTEST_END
		
		`SVTEST("CRM send with too early timeout NR")
			_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(tdma_scheme_crm::valid());
			_top_config._check_receive_crm.expect_no_crm_response();
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(.number_of_commands(1), .bc(1'b1)));
			common_config.timeout_crm_nr = 250;
			#0.5ms;
			`FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(busy, 1'b0);
		`SVTEST_END
			
		`SVTEST("CRM send with CRC enabled")
			common_config.crc_enable = 1'b1;
			update_master_config();
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(.number_of_commands(1), .bc(1'b0)));
			#0.5ms;
			`FAIL_IF(get_errors() > 0)
		`SVTEST_END
			
		`SVTEST("CRM receive")
			_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(tdma_scheme_crm::valid_with_data('h0bad, 'hc0de, 3,));
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(.number_of_commands(1), .bc(1'b0)));
			#0.5ms;
			`FAIL_IF(get_errors() > 0)
		`SVTEST_END
			
		`SVTEST("CRM receive with CRC error")
			_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(tdma_scheme_crm::paket_with_CRC_error(16'($urandom()), 16'($urandom()), 3));
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(null, 1));
			#0.5ms;
			`FAIL_IF(get_errors() > 0)
		`SVTEST_END
		
		for (int symbols=1; symbols<13; symbols++) begin
			`SVTEST($sformatf("CRM receive with %2d symbols", symbols))
				_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(create_scheme_with_packet(tdma_scheme_packet_crm::new_packet(285, 305, symbols)));
				_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(null, 1));
				#0.5ms;
				`FAIL_IF(get_errors() > 0)
                `FAIL_UNLESS_EQUAL(busy, '0)
			`SVTEST_END
		end
		
		for (int symbols = 9; symbols<17; symbols++) begin
			`SVTEST($sformatf("CRM receive with late response and %d symbols", symbols))
                dsi3_slave_tr   response = new();
                tdma_scheme scheme = crm_slave_scheme(.start_time(370), .symbols(symbols));
                response.data = scheme.packets[0].packet.data;
                while (response.data.size() > 8)
                    void'(response.data.pop_back());
                response.symbol_coding_error = 1'b0;
                response.end_tr($realtime+370.0us);
				_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(scheme);
				fork
                    _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(null, 1));
                    begin
                        #300us;
                        _top_config._check_receive_crm.set_slave_response(response);
                    end
                join
				#0.6ms;
				`FAIL_IF(get_errors() > 0)
			`SVTEST_END
		end
		
		`SVTEST($sformatf("CRM receive 2 packets in CRM"))
            common_config.timeout_crm = 500;
            update_master_config();
			_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(crm_slave_scheme_with_two_responses(.symbols(8)));
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(null, 1));
			#0.6ms;
			`FAIL_IF(get_errors() > 0)
		`SVTEST_END
			
		for(int start_time = 265; start_time <= 370; start_time += 1) begin
			`SVTEST($sformatf("CRM early/normal/late slave response after %0dus", start_time))
				tdma_scheme scheme;
				scheme = tdma_scheme_crm::valid_with_data(16'($urandom_range(16'hffff,0)), 16'($urandom_range(16'hffff,0)));
				scheme.packets[0].earliest_start_time = start_time;
				scheme.packets[0].latest_start_time = start_time+1;	
				scheme.packets[0].set_tolerance(1.0);
				scheme.packets[0].set_tolerance_limits(0.999, 1.001);
				scheme.packets[0].tolerance_int = 1000;
				_top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(scheme);
				_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(null, 1));
				#0.5ms;
				`FAIL_IF(get_errors() > 0)
			`SVTEST_END
        end
        
        `SVTEST($sformatf("CRM receive long packets over timeout"))
            dsi3_slave_tr   response = new();
            tdma_scheme scheme = crm_slave_scheme(.start_time(295), .symbols(100));
            response.data = scheme.packets[0].packet.data;
            while (response.data.size() > 'h10)
                void'(response.data.pop_back());
            response.symbol_coding_error = 1'b0;
            response.begin_tr($time() + 295us);
            _top_config._check_receive_crm.master_start_time = $time();
            _top_config._check_receive_crm.set_slave_response(response);
            _top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(scheme);
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(null, 1));
            #((295us+100*3*3us+40us)*1.05);
            response.end_tr();
            `FAIL_UNLESS_EQUAL(busy, '0)
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        `SVTEST($sformatf("CRM receive late packets at timeout"))
            tdma_scheme scheme;
            scheme = tdma_scheme_crm::valid_with_data(.high_word(16'($urandom_range(16'hffff,0))), .low_word(16'($urandom_range(16'hffff,0))), .chiptime(5));
            common_config.chip_time = CHIPTIME_5US;
            update_master_config();
            scheme.packets[0].earliest_start_time = 308;
            scheme.packets[0].latest_start_time = 308; 
            scheme.packets[0].set_tolerance(1.0);
            scheme.packets[0].set_tolerance_limits(0.999, 1.001);
            scheme.packets[0].tolerance_int = 1000;
            _top_config._dsi3_slave_agent.m_crm_tdma_scheme_port.write(scheme);
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_crm_commands_bc(null, 1));
            #0.6ms;
            `FAIL_UNLESS_EQUAL(busy, '0)
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        //FIXME: add test case for too short timeout thus empty packet should be stored (P52144-164)
        
        //FIXME: more than 8 symbols but late thus 8 symbols were received until timeout -> SCE!?
        
		`endif
		
        `ifndef NO_TDMA_TESTS
		//##########   TDMA   ###################################################
		for (int loop = 1; loop <= 30; loop++) begin
			`SVTEST($sformatf("TDMA packet upload %1d", loop))
				spi_command_frame_seq new_frame = new();
				spi_upload_tdma_packet_seq tdma_packet_seq;
				tdma_packet_seq = spi_seq_factory#(spi_upload_tdma_packet_seq)::create_seq();
				tdma_packet_seq.channel_bits = '1;
				new_frame.add_command(tdma_packet_seq);
				_frame_facade.start_this(new_frame); //spi_frame_factory_with_single_command#(spi_upload_tdma_packet_seq)::create_frame(null));
				#1us;
				`FAIL_IF(get_errors() > 0)
			`SVTEST_END
		end
		
//		for (int loop = 1; loop <= 30; loop++) begin
//			`SVTEST($sformatf("TDMA validate %1d", loop))
//				spi_command_frame_seq new_frame = new();
//				spi_validate_tdma_scheme_seq tdma_validate_seq;
//				tdma_validate_seq = spi_seq_factory#(spi_validate_tdma_scheme_seq)::create_seq();
//				tdma_validate_seq.channel_bits = '1;
//				new_frame.add_command(tdma_validate_seq);
//				_frame_facade.start_this(new_frame);
//				#50us;
//				`FAIL_IF(get_errors() > 0)
//			`SVTEST_END
//		end

        `SVTEST("TDMA validate - with period of less than 100us")
            tdma_scheme_pdcm scheme = new();
            void'(scheme.randomize() with {packets.size() == 1; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;});
            scheme.pdcm_period = 1;
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
            #20us;
            `FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b0)
            `FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(100))
            word_count = get_word_count_of_scheme(scheme);
            `FAIL_UNLESS_EQUAL(tdma_frame_word_count, word_count)
            `FAIL_IF(get_errors() > 0)
            `FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
        `SVTEST_END
        
        `SVTEST("TDMA validate - with period of more than 65500us")
            tdma_scheme_pdcm scheme = new();
            void'(scheme.randomize() with {packets.size() == 1; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;});
            scheme.pdcm_period = 'hFFFF;
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
            #20us;
            `FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b0)
            word_count = get_word_count_of_scheme(scheme);
            `FAIL_UNLESS_EQUAL(tdma_frame_word_count, word_count)
            `FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(16'hFFF0))
            `FAIL_IF(get_errors() > 0)
            `FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
        `SVTEST_END
		
		`SVTEST("TDMA validate - Denso")
			tdma_scheme_pdcm_denso denso_scheme = new();
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(denso_scheme), .add_crc_command(1'b0)));
			#20us;
			`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b0)
			`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(denso_scheme.pdcm_period))
			`FAIL_UNLESS_EQUAL(tdma_frame_word_count, 22)
            `FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
		`SVTEST_END
		
		`SVTEST($sformatf("TDMA validate with 0 packets -> fail"))
			begin // have a valid scheme loaded
				tdma_scheme_pdcm_denso denso_scheme = new();
				_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(denso_scheme), .add_crc_command(1'b0)));
				#20us;
				`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b0)
			end
			begin
				spi_command_frame_seq new_frame = new();
				spi_validate_tdma_scheme_seq tdma_validate_seq;
				tdma_validate_seq = spi_seq_factory#(spi_validate_tdma_scheme_seq)::create_seq();
				tdma_validate_seq.channel_bits = '1;
				tdma_validate_seq.packet_count = 0;
				new_frame.add_command(tdma_validate_seq);
				_frame_facade.start_this(new_frame);
				#20us;
                `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
				`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
				`FAIL_IF(get_errors() > 0)
				`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
			end
		`SVTEST_END
		
		`SVTEST("TDMA validate - single packet and fail")
			tdma_scheme_pdcm scheme = tdma_scheme_pdcm_factory::single_packet_with_words('{16'haffe, 16'hb0b0});
			scheme.pdcm_period = 50;
			scheme.packets[0].latest_start_time = 101;
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
			#20us;
			`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
            `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
			`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(100))
			`FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
		`SVTEST_END
		
		`SVTEST("TDMA validate - single packet")
			tdma_scheme_pdcm scheme = tdma_scheme_pdcm_factory::single_packet_with_words('{16'haffe, 16'hb0b0});
			scheme.pdcm_period = 200;
			_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
			#20us;
			`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b0)
			`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
            word_count = get_word_count_of_scheme(scheme);
            `FAIL_UNLESS_EQUAL(tdma_frame_word_count, word_count)
			`FAIL_IF(get_errors() > 0)
			`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
		`SVTEST_END
		
        for (int loop = 0; loop < 50; loop++) begin
            `SVTEST($sformatf("TDMA validate - random valid scheme (%3d)", loop))
                tdma_scheme_pdcm scheme = new();
                void'(scheme.randomize() with {packets.size() inside {[1:15]}; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;});
                _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
                #20us;
                `FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b0)
                `FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
                word_count = get_word_count_of_scheme(scheme);
                `FAIL_UNLESS_EQUAL(tdma_frame_word_count, word_count)
                `FAIL_IF(get_errors() > 0)
                `FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
            `SVTEST_END
        end
		
		//FIXME: invalidate scheme with packet upload
		
		for (int packets=1; packets<16; packets++) begin
			time wait_time=50us;
			packet_position_e	packet_position = packet_position.first;
			do begin
				automatic int	position;
				position = get_packet_position(packet_position, packets);
				$display("position=%1d", position);
				
				`SVTEST($sformatf("TDMA invalid by earliest = 0 at %s(%1d) and %1d packets", packet_position.name, position, packets))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].earliest_start_time = 0;
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by latest = 0 at %s(%1d) and %1d packets", packet_position.name, position, packets))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].latest_start_time = 0;
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by symbol count = 0 at %s(%1d) and %1d packets", packet_position.name, position, packets))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].symbol_count = 0;
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by earliest greater than period at %s(%1d)", packet_position.name, position))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].earliest_start_time = scheme.pdcm_period + $urandom_range(200,1);
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by latest greater than period at %s(%1d)", packet_position.name, position))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].latest_start_time = scheme.pdcm_period + $urandom_range(200,1);
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by earliest equal to period at %s(%1d)", packet_position.name, position))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].earliest_start_time = scheme.pdcm_period;
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by latest equal to period at %s(%1d)", packet_position.name, position))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].latest_start_time = scheme.pdcm_period;
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by symbol count smaller than 4 at %s(%1d)", packet_position.name, position))
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					scheme.packets[position].symbol_count = $urandom_range(3,1);
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				`SVTEST($sformatf("TDMA invalid by earliest greater than latest at %s(%1d)", packet_position.name, position))
					int temp;
					tdma_scheme_pdcm scheme = create_valid_scheme(packets);
					temp = scheme.packets[position].latest_start_time;
					scheme.packets[position].latest_start_time = scheme.packets[position].earliest_start_time;
					scheme.packets[position].earliest_start_time = temp;
					_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
					#(wait_time);
					`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                    `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
					`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
					`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
				`SVTEST_END
				
				if ((packets > 2) && (position != get_packet_position(LAST_PACKET, packets))) begin
					`SVTEST($sformatf("TDMA invalid by latest N > earliest N+1 at %s(%1d)", packet_position.name, position))
						int temp;
						tdma_scheme_pdcm scheme = create_valid_scheme(packets);
						temp = scheme.packets[position].latest_start_time;
						scheme.packets[position].latest_start_time = scheme.packets[position+1].earliest_start_time;
						scheme.packets[position+1].earliest_start_time = temp;
						_frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_tdma_scheme(.scheme(scheme), .add_crc_command(1'b0)));
						#(wait_time);
						`FAIL_UNLESS_EQUAL(no_tdma_scheme_defined, 1'b1)
                        `FAIL_UNLESS_EQUAL(tdma_frame_word_count, 0)
						`FAIL_UNLESS_EQUAL(i_dsi3_block.DSI3_channel_registers_PDCM_PERIOD.PDCMPER, shortint'(scheme.pdcm_period))
						`FAIL_UNLESS_EQUAL(i_dsi3_block.i_tdma_manager.state, S_IDLE)
					`SVTEST_END
				end
				
				packet_position = packet_position.next();
			end while (packet_position != packet_position.first);
        end
        
        `endif
        
        `ifndef NO_PDCM_TEST
        //##########   PDCM   ###################################################
        `SVTEST("PDCM send DENSO")
            tdma_scheme_pdcm_denso denso_scheme = new();
            tdma_scheme_pdcm_denso slave_denso_scheme = new();
            upload_scheme(denso_scheme);
            #20us;
            foreach(slave_denso_scheme.packets[i]) begin : relax_timing_to_not_get_unexpected_TE_flags
                slave_denso_scheme.packets[i].earliest_start_time +=10;
                slave_denso_scheme.packets[i].latest_start_time -=10;
            end
            _top_config._check_receive_pdcm.initialize();
            _top_config._dsi3_slave_agent.m_config.pdcm_scheme = slave_denso_scheme;
            set_tdma_scheme(denso_scheme);
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 5));
            #6ms;
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        for (int long_packet = 0; long_packet < 7; long_packet++) begin
            `SVTEST($sformatf("PDCM with long packets at position %1d", long_packet))
                tdma_scheme_pdcm_denso denso_scheme = new();
                tdma_scheme_pdcm_denso slave_denso_scheme = new();
                denso_scheme.pdcm_period += 200;
                slave_denso_scheme.pdcm_period += 200;
                upload_scheme(denso_scheme);
                #20us;
                _top_config._check_receive_pdcm.initialize();
                set_tdma_scheme(denso_scheme);
                slave_denso_scheme.packets[long_packet].symbol_count = 20;
                if (long_packet < 6)
                    slave_denso_scheme.packets[long_packet+1].enable = 1'b0;
                fill_scheme_with_data(slave_denso_scheme);
                foreach(slave_denso_scheme.packets[i]) begin : relax_timing_to_not_get_unexpected_TE_flags
                    slave_denso_scheme.packets[i].earliest_start_time +=10;
                    slave_denso_scheme.packets[i].latest_start_time -=10;
                end
                _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(slave_denso_scheme);
//                _top_config._check_receive_pdcm.set_frame(slave_denso_scheme);
                
                _top_config._check_receive_pdcm.set_defined_slave_answer();
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER, 16'h0000);
                for (int i = 0; i < 7; i++) begin
                    if (slave_denso_scheme.packets[i].is_enabled()) begin
                        logic[15:0] data[$];
                        void'(convert_queue #(4, 16)::convert(slave_denso_scheme.packets[i].packet.data, data));
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER, 16'h2004, i);
                        for (int k = 0; k < 2; k++) begin
                            _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, data[k]);
                        end
                        if (i==long_packet) _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, 16'h2014, i);
                        else                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, 16'h0008, i);
                    end
                    else begin
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER, 16'h2000, i);
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, 16'h0000, i);
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, 16'h0000, i);
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, 16'h2000, i);
                    end
                end
                if (long_packet == 6) _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN, 16'h0007);
                else                  _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN, 16'h0006);
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_VALIDATE, 0);
                
                _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 2));
                #2.5ms;
                `FAIL_IF(get_errors() > 0)
            `SVTEST_END
        end
        
        `SVTEST("PDCM - receive more packets than defined in scheme -> PC flag in frame header")
            tdma_scheme_pdcm_denso denso_scheme = new();
            tdma_scheme_pdcm_denso slave_denso_scheme = new();
            slave_denso_scheme.pdcm_period += 300;
            denso_scheme.pdcm_period += 300;
            upload_scheme(denso_scheme);
            #20us;
            _top_config._check_receive_pdcm.initialize();
            _top_config._dsi3_slave_agent.m_config.pdcm_scheme = slave_denso_scheme;
            foreach(slave_denso_scheme.packets[i]) begin : relax_timing_to_not_get_unexpected_TE_flags
                slave_denso_scheme.packets[i].earliest_start_time +=10;
                slave_denso_scheme.packets[i].latest_start_time -=10;
            end
            slave_denso_scheme.add_packet(tdma_scheme_packet_pdcm::new_packet(975, 1015, 8, dsi3_pkg::SID_8Bit));
            set_tdma_scheme(denso_scheme);
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
            #6ms;
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        for (int long_packet = 0; long_packet < 7; long_packet++) begin
            for (int symbols = 4; symbols < 11; symbols++) begin
                if (symbols != 8) begin
                    `SVTEST($sformatf("PDCM - slave response %1d other symbol count than defined (%1d symbols)", long_packet, symbols))
                        tdma_scheme_pdcm_denso denso_scheme = new();
                        tdma_scheme_pdcm_denso slave_denso_scheme = new();
                        upload_scheme(denso_scheme);
                        #20us;
                        _top_config._check_receive_pdcm.initialize();
                        set_tdma_scheme(denso_scheme);
                        slave_denso_scheme.packets[long_packet].symbol_count = symbols;
                        fill_scheme_with_data(slave_denso_scheme);
                        foreach(slave_denso_scheme.packets[i]) begin : relax_timing_to_not_get_unexpected_TE_flags
                            slave_denso_scheme.packets[i].earliest_start_time +=10;
                            slave_denso_scheme.packets[i].latest_start_time -=10;
                        end
                        _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(slave_denso_scheme);
                        
                        _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
                        #1.2ms;
                        `FAIL_IF(get_errors() > 0)
                    `SVTEST_END
                end
            end
        end
        
        for (int long_packet = 0; long_packet < 7; long_packet++) begin
            for (int symbols = 2; symbols < 4; symbols++) begin
                if (symbols != 8) begin
                    `SVTEST($sformatf("PDCM - slave response %1d other symbol count than defined (%1d symbols)", long_packet, symbols))
                        tdma_scheme_pdcm_denso denso_scheme = new();
                        tdma_scheme_pdcm_denso slave_denso_scheme = new();
                        upload_scheme(denso_scheme);
                        #20us;
                        _top_config._check_receive_pdcm.initialize();
                        set_tdma_scheme(denso_scheme);
                        slave_denso_scheme.packets[long_packet].symbol_count = symbols;
                        fill_scheme_with_data(slave_denso_scheme);
                        foreach(slave_denso_scheme.packets[i]) begin : relax_timing_to_not_get_unexpected_TE_flags
                            slave_denso_scheme.packets[i].earliest_start_time +=10;
                            slave_denso_scheme.packets[i].latest_start_time -=10;
                        end
                        _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(slave_denso_scheme);
                        
                        
                        _top_config._check_receive_pdcm.set_defined_slave_answer();
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER, 16'h0000);
                        for (int i = 0; i < 7; i++) begin
                            if (i!=long_packet) begin
                                logic[15:0] data[$];
                                void'(convert_queue #(4, 16)::convert(slave_denso_scheme.packets[i].packet.data, data));
                                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER, 16'h2004);
                                for (int k = 0; k < 2; k++) begin
                                    _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, data[k]);
                                end
                                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, 16'h0008);
                            end
                            else begin
                                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER, 16'h2000);
                                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, 16'h0000, i);
                                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, 16'h0000, i);
                                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, 16'h2000, i);
                            end
                        end
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN, 16'h0006);
                        _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_VALIDATE, 0);
                        
                        _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
                        #1.2ms;
                        `FAIL_IF(get_errors() > 0)
                    `SVTEST_END
                end
            end
        end
        
        for(int symbol_count = 255; symbol_count < 260; symbol_count++) begin
            `SVTEST($sformatf("PDCM - receive more than 255 symbols (%1d)", symbol_count))
                tdma_scheme_pdcm scheme = new();
                if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 255; symbol_count_max == 255; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) begin
                    `FAIL_IF_LOG(1, "failed to randomize TDMA scheme")
                end
                scheme.pdcm_period = scheme.pdcm_period + 100;
                upload_scheme(scheme);
                scheme.packets[0].symbol_count = symbol_count;
                #20us;
                _top_config._check_receive_pdcm.initialize();
                _top_config._dsi3_slave_agent.m_config.pdcm_scheme = scheme;
                set_tdma_scheme(scheme);
                _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
                #3.3ms;
                `FAIL_IF(get_errors() > 0)
            `SVTEST_END
        end
        
        for (int se_packet_index = 0; se_packet_index < 16; se_packet_index++) begin
            `SVTEST($sformatf("PDCM - receive response with symbol coding error (slave %1d)", se_packet_index))
                tdma_scheme_pdcm_denso_15 scheme = new();
                tdma_scheme_pdcm_denso_15 scheme_slaves = new();
                upload_scheme(scheme);
                set_tdma_scheme(scheme);
                set_symbol_coding_error(scheme, se_packet_index);
                #20us;
                foreach(scheme_slaves.packets[i]) begin : relax_timing_to_not_get_unexpected_TE_flags
                    scheme_slaves.packets[i].earliest_start_time +=10;
                    scheme_slaves.packets[i].latest_start_time -=10;
                end
                _top_config._check_receive_pdcm.initialize();
                _top_config._dsi3_slave_agent.m_config.pdcm_scheme = scheme_slaves;
                _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
                #2.2ms;
                `FAIL_IF(get_errors() > 0)
            `SVTEST_END
        end
        
        `SVTEST($sformatf("PDCM - receive very late response in last packet"))
            begin : upload_scheme_into_block
                tdma_scheme_pdcm scheme = new();
                void'(scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;});
                scheme.packets[0].id_symbol_count = dsi3_pkg::SID_8Bit;
                scheme.pdcm_period = 300;
                upload_scheme(scheme);
                #20us;
                _top_config._check_receive_pdcm.initialize();
            end
            begin
                dsi3_pdcm_packet packet = new();
                tdma_scheme_pdcm scheme = new();
                void'(packet.randomize() with {data.size() == 8; source_id_symbols == dsi3_pkg::SID_8Bit;});
                scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet);
                scheme.pdcm_period = 300;
                scheme.packets[0].earliest_start_time = 250;
                scheme.packets[0].latest_start_time = 250 + 5;
                _top_config._dsi3_slave_agent.m_config.pdcm_scheme = scheme;
                set_tdma_scheme(scheme);
            end
            begin : define_received_data
                _top_config._check_receive_pdcm.set_defined_slave_answer();
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER, 16'h0000,1);
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER, 16'h2800,2);
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, 16'h0000,3);
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE, 16'h0000,4);
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, 16'h2800,5);
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN, 16'h0001,6);
                _top_config._check_receive_pdcm.create_buffer_access(PDCM_BUFFER_VALIDATE, 0,7);
            end
            
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
            #0.4ms;
            _top_config._check_receive_pdcm.clear_transmissions();
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        `SVTEST($sformatf("PDCM - with symbol noise"))
            tdma_scheme_pdcm_with_symbol_noise scheme_with_noise  = new();
            tdma_scheme_pdcm_without_noise scheme_without_noise = new();
            upload_scheme(scheme_without_noise);
            #20us;
            _top_config._check_receive_pdcm.initialize();
            _top_config._dsi3_slave_agent.m_config.pdcm_scheme = scheme_with_noise;
            set_tdma_scheme(scheme_without_noise);
            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
            #1.2ms;
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        `SVTEST($sformatf("PDCM - packets start before t__PDCM,START__"))
            tdma_scheme_pdcm scheme  = new();
            dsi3_pdcm_packet packet = new();
            void'(scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;});
            scheme.packets[0].id_symbol_count = dsi3_pkg::SID_8Bit;
            scheme.pdcm_period = 200;
            upload_scheme(scheme);
            #20us;
            
            void'(packet.randomize() with {data.size() == 8; source_id_symbols == dsi3_pkg::SID_8Bit;});
            _top_config._check_receive_pdcm.initialize();
            _top_config._dsi3_slave_agent.m_config.pdcm_scheme = tdma_scheme_pdcm_factory::no_answer();
            set_tdma_scheme(scheme);
            fork
                _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
                begin
                    #16us;
                    send_slave_packet(packet);
                end
            join
            #0.3ms;
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        `SVTEST($sformatf("PDCM - packets start before t__PDCM,START__ with correct TDMA scheme"))
            tdma_scheme_pdcm scheme  = new();
            dsi3_pdcm_packet packet = new();
            void'(scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;});
            scheme.packets[0].id_symbol_count = dsi3_pkg::SID_8Bit;
            scheme.packets[0].earliest_start_time = 10;
            scheme.packets[0].latest_start_time = 30;
            scheme.pdcm_period = 200;
            upload_scheme(scheme);
            #20us;
            
            void'(packet.randomize() with {data.size() == 8; source_id_symbols == dsi3_pkg::SID_8Bit;});
            _top_config._check_receive_pdcm.initialize();
            _top_config._dsi3_slave_agent.m_config.pdcm_scheme = tdma_scheme_pdcm_factory::no_answer();
            set_tdma_scheme(scheme);
            fork
                _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
                begin
                    #16us;
                    send_slave_packet(packet);
                end
            join
            #0.3ms;
            `FAIL_IF(get_errors() > 0)
        `SVTEST_END
        
        
        
        //FIXME: x Pakete auslassen (mögliche Positionen ausprobieren)
//        for (int number_of_missing_packets = 0; number_of_missing_packets < 7; number_of_missing_packets++) begin
//            `SVTEST($sformatf("PDCM with %1d missing packets", number_of_missing_packets))
//                tdma_scheme_pdcm_denso denso_scheme = new();
//                tdma_scheme_pdcm_denso slave_denso_scheme = new();
//                upload_scheme(denso_scheme);
//                set_tdma_scheme(denso_scheme);
//                slave_denso_scheme.packets[number_of_missing_packets].symbol_count = 20;
//                if (number_of_missing_packets < 6)
//                    slave_denso_scheme.packets[number_of_missing_packets+1].enable = 1'b0;
//                _top_config._dsi3_slave_agent.m_config.pdcm_scheme = slave_denso_scheme;
//                _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 2));
//                #2.5ms;
//                `FAIL_IF(get_errors() > 0)
//            `SVTEST_END
//        end
        
        //FIXME: ein Paket zu spät (alle Pakete mal verschieben)
        //FIXME: ein Paket auslassen (alle Positionen ausprobieren)
        //FIXME: gar keine Pakete empfangen
        //FIXME: ein Slave prabbelt bis zum Anfang des nächsten Paketes
        //FIXME: ein Slave prabbelt bis über das nächste Paket
        //FIXME: check all CRC variants (fail + correct)
        //FIXME: 
        //FIXME: 
              
//      for (int symbols=1; symbols<4; symbols++) begin
//          `SVTEST($sformatf("PDCM with less than 4 symbols (%1d)",symbols))
//              set_pdcm_period(500);
//              update_master_config();
//              _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(create_scheme_with_packet(tdma_scheme_packet::new_packet(50, 60, symbols, 0)));
//              _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
//              #0.6ms;
//              `FAIL_IF(get_errors() > 0)
//          `SVTEST_END
//      end
//      
//      for (int symbols=254; symbols<265; symbols++) begin
//          `SVTEST($sformatf("PDCM with more than 255 symbols (%1d)",symbols))
//              set_pdcm_period(2600);
//              update_master_config();
//              _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(create_scheme_with_packet(tdma_scheme_packet::new_packet(50, 60, symbols, 0)));
//              _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
//              #3ms;
//              `FAIL_IF(get_errors() > 0)
//          `SVTEST_END
//      end
//      
//      //FIXME: sweep over timeout (period)
//      //FIXME: set tolerance of slave answer to 1.000
////        `SVTEST($sformatf("PDCM with 258 symbols at receive timeout"))
////            set_pdcm_period(2370);
////            update_master_config();
////            _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(create_scheme_with_packet(tdma_scheme_packet::new_packet(60, 60, 258, 0)));
////            _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
////            #3ms;
////            `FAIL_IF(get_errors())
////        `SVTEST_END

//FIXME: check and add me again
//      for(int start_time = 120; start_time <= 190; start_time += 1) begin
//          for(int fine_delay = 0; fine_delay < 1000; fine_delay += 50) begin
//              `SVTEST($sformatf("late slave answer after %0dus + %0dns", start_time, fine_delay))
//                  dsi3_pdcm_packet packets;
//                  common_config.sid_length = 2;
//                  set_pdcm_period(200);
//                  begin
//                      tdma_scheme scheme;
//                      dsi3_pdcm_packet next_packet = new();
//                      if(!next_packet.randomize() with {data.size() == 8; source_id_symbols == 2;})begin
//                          `FAIL_IF_LOG(1, "randomization error")
//                      end
//          
//                      scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(next_packet);
//                      scheme.packets[0].earliest_start_time = start_time;
//                      scheme.packets[0].latest_start_time = start_time+3; 
//                      scheme.packets[0].fine_delay_time = fine_delay * 1ns;
//                      scheme.packets[0].tolerance_int = 1000;
//                      packets = next_packet;
//                      _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(scheme);
//                  
//                      //transaction_recorder.clear_all(); // FIXME: add me!
//                      
//                      _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 1));
//                      #300us;
//                      `FAIL_IF(get_errors() > 0)
//                  end
//                  #100us;
//              `SVTEST_END
//          end
//      end

        //FIXME: check and add me again
//      `SVTEST($sformatf("split packets in PDCM if long and too late"))
//          set_pdcm_period(1500);
//          update_master_config();
//          _top_config._dsi3_slave_agent.m_pdcm_tdma_scheme_port.write(create_scheme_with_packet(tdma_scheme_packet::new_packet(50, 60, 200, 0)));
//          _frame_facade.start_this(spi_frame_factory#(0)::create_frame_with_a_pdcm_command(null, 2));
//          #3ms;
//          `FAIL_IF(get_errors())
//      `SVTEST_END
        
        `endif
        
        for (int expected_dac_value = 0; expected_dac_value < 'h22; expected_dac_value++) begin
            `SVTEST($sformatf("Quiescent current - check current (DAC=%1d)", expected_dac_value))
                spi_command_frame_seq new_frame = new();
                spi_measure_quiescent_current_seq  iq_seq = spi_seq_factory#(spi_measure_quiescent_current_seq)::create_seq();
                DSI_IRQ_STAT_t  stat;
                DSI_IRQ_MASK_t  mask = '1;
                mask.IQ_ERR = 1'b0;
                rx_dac = expected_dac_value;
                write_elip(ADDR_DSI_0_DSI_IRQ_STAT, 16'hffff); // clear interrupts
                wait_for_n_clocks(5);
                iq_seq.channel_bits = 2'b01;
                new_frame.add_command(iq_seq);
                _frame_facade.start_this(new_frame);
                #0.01ms;
                `FAIL_UNLESS_EQUAL(busy, 1'b1);
                #0.05ms;
                `FAIL_UNLESS_EQUAL(busy, 1'b0);
                #0.01ms;
                if (expected_dac_value == 0) begin
                    `FAIL_UNLESS_EQUAL(dsi3_io.rx_idac, 0)
                end
                else begin
                    if (expected_dac_value > 'h20) begin
                        `FAIL_UNLESS_EQUAL(dsi3_io.rx_idac, 5'h1f)
                    end 
                    else begin
                        `FAIL_UNLESS_EQUAL(dsi3_io.rx_idac, expected_dac_value - 1)
                    end
                end
                if ((expected_dac_value > 'h1f)) begin
                    `FAIL_UNLESS_EQUAL(interrupt, 1'b1)
                    read_elip(ADDR_DSI_0_DSI_IRQ_STAT, stat);
                    `FAIL_UNLESS_EQUAL(stat.IQ_ERR, 1'b1);
                    write_elip(ADDR_DSI_0_DSI_IRQ_MASK, mask); // mask interrupt
                    `FAIL_UNLESS_EQUAL(interrupt, 1'b0)
                    write_elip(ADDR_DSI_0_DSI_IRQ_MASK, 16'hffff); // unmask interrupt
                    `FAIL_UNLESS_EQUAL(interrupt, 1'b1)
                    write_elip(ADDR_DSI_0_DSI_IRQ_STAT, 16'hffff); // clear interrupts
                    `FAIL_UNLESS_EQUAL(interrupt, 1'b0)
                end
                else begin
                    `FAIL_UNLESS_EQUAL(interrupt, 1'b0)
                end
                `FAIL_IF(get_errors() > 0)
            `SVTEST_END
        end
			
		//TODO: check hardware error and debouncing!
		
		//TODO: check interrupt
		
		//TODO: check transmit_pending
	end	 
	`SVUNIT_TESTS_END
	
endmodule
