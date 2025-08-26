`include "svunit_defines.svh"
`include "clk_rst_define.sv"

module command_control_test import project_pkg::*; ();
	
	`include "uvm_macros.svh"
	
	import svunit_pkg::svunit_testcase;
	import svunit_uvm_mock_pkg::*;
	import crc_calculation_pkg::spi_crc_ccitt_16;
	import addresses_pkg::*;
	import common_test_pkg::*;
	import uvm_pkg::*;
	import buffer_reader_pkg::*;
	import buffer_writer_pkg::*;
	import spi_pkg::*;
	import unit_test_pkg::*;

	string name = "command_control_test";
	svunit_testcase svunit_ut;
	
	top_config		_top_config;
	
	ecc_error_if #(.WIDTH (1)) buf_ecc_error (), cmd_ecc_error();
	
	`clk_def(27777ps)
	
	buffer_reader_if spi_command_reader ();
	buffer_writer_if spi_command_writer ();
	buffer_writer_if dsi_command_writer[DSI_CHANNELS-1:0] ();
	
	elip_full_if	elip_command_buffer ();
	elip_full_if	elip_write_register ();
	elip_bus_if		elip_bus_register();
	elip_bus_if		elip_bus_buffer();
	
	elip_if #(.addr_width  (16 ), .data_width  (16 )) elip_registers ();
	
	
	dsi_logic_if	clear_crm_data_buffer ();
	dsi_logic_if	clear_pdcm_data_buffer ();
	dsi_logic_if	clear_command_buffer ();
	
	frame_facade	_frame_facade;
	
	dsi_logic_t		clear_command_queue;
	
	bit[DSI_CHANNELS-1:0] initial_begin_of_channel_done;
	
	command_control_to_dsi3_if to_dsi3 ();
	
	dsi_logic_t	dsi3_enabled;
	
	generate
		genvar k;
		for (k=0; k< DSI_CHANNELS; k++) begin : generate_dsi_config_connections
			initial begin
				if (initial_begin_of_channel_done == '0) begin
					_top_config = new("_top_config");
					uvm_config_db #(top_config)::set(null, "uvm_test_top", "_top_config", _top_config);
					uvm_config_db #(top_config)::set(null, "uvm_test_top.m_env", "_top_config", _top_config);
			
					_top_config._spi_writer_config.vif = spi_command_writer;
					_top_config._spi_writer_config.vif_clk_rst = clk_rst;
					
					_top_config._clear_crm_data_buffer = clear_crm_data_buffer;
					_top_config._clear_pdcm_data_buffer = clear_pdcm_data_buffer;
					_top_config._clear_command_buffer = clear_command_buffer;
					
					for (int i=0; i<DSI_CHANNELS; i++) begin
						_top_config._dsi_writer_config[i].vif_clk_rst = clk_rst;
					end
			
					_top_config._elip_command_config.vif	= elip_bus_buffer;
					_top_config._elip_register_config.vif	= elip_bus_register;
					
					_top_config._command_reader_config.vif = spi_command_reader;
					_top_config._command_reader_config.vif_clk_rst = clk_rst;
				end
		
				_top_config._dsi_writer_config[k].vif = dsi_command_writer[k];
				if ($onehot(~initial_begin_of_channel_done))
					run_test();
				initial_begin_of_channel_done[k] = 1'b1;
			end
		end
	endgenerate
	
	initial dsi3_enabled = '1;
	initial clear_command_queue='0;
	
	interface_converter_elip_full_2_elip_bus i_interface_converter_write_register (
		.clk_rst    (clk_rst.slave             ),
		.elip_full  (elip_write_register.slave ), 
		.elip_bus   (elip_bus_register         ));
	
	interface_converter_elip_full_2_elip_bus i_interface_converter_cmd_buffer (
		.clk_rst    (clk_rst.slave             ),
		.elip_full  (elip_command_buffer.slave ), 
		.elip_bus   (elip_bus_buffer  ));
	
	//===================================
	// This is the UUT that we're 
	// running the Unit Tests on
	//===================================
	command_control i_command_control (
		.clk_rst              (clk_rst.slave              ), 
		.elip_write_register  (elip_write_register.master ), 
		.command_reader       (spi_command_reader.master  ), 
		.dsi_command_writer   (dsi_command_writer.master  ),
		.to_dsi3              (to_dsi3.master             ),
		.ecc_error            (cmd_ecc_error.master       ),
		.i_clear_dsi3_command_queue(clear_command_queue   ),
		.o_hw_fail            (                           ), //TODO: test me
		.o_clear_command_queue(                           ));//TODO: test me
	
	assign	to_dsi3.dsi3_enabled = dsi3_enabled;
	assign	clear_crm_data_buffer.D = to_dsi3.clear_crm_data_buffer;
	assign	clear_pdcm_data_buffer.D = to_dsi3.clear_pdcm_data_buffer;
	assign	clear_command_buffer.D = to_dsi3.stop_transmission;
		
	buffer #(
		.BASE_ADDR                  ('d0                        ), 
		.ADDR_WIDTH                 (16                         ), 
		.BUFFER_OFFSET_ADDRESS      ('h1000                     ), 
		.BUFFER_SIZE                ('h100                      ), 
		.PRIORITY_READ              (1'b0                       )
	) i_buffer (
		.clk_rst                    (clk_rst.slave              ), 
		.reader                     (spi_command_reader.slave   ), 
		.writer                     (spi_command_writer.slave   ), 
		.elip                       (elip_command_buffer.master ), 
		.elip_registers             (elip_registers.slave       ), 
		.o_elip_registers_data_out  (                           ),
		.o_data_available           (                           ),
		.ecc_error                  (buf_ecc_error.master       ));
	
	// model for the RAM to store data
	ram_model ram_model (
		.clk_rst   (clk_rst.slave  ), 
		.elip      (elip_command_buffer.slave     ) 
	);
	
	ram_model i_register_model(
		.clk_rst   (clk_rst.slave  ), 
		.elip      (elip_write_register.slave     ) 
	);
	
	assign	elip_registers.addr = '0;
	assign	elip_registers.data_write = '0;
	assign	elip_registers.wr = 1'b0;
	assign	elip_registers.rd = 1'b0;
	
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
		if (_frame_facade == null)
			_frame_facade = _top_config._frame_facade;
		
		_top_config._check_register_write.initialize();
		_top_config._check_elip_command_write.initialize();
		foreach (_top_config._check_dsi_command_writes[i]) begin
			_top_config._check_dsi_command_writes[i].initialize();
		end
		uvm_report_mock::setup();
		dsi3_enabled = '1;
		clear_command_queue = '0;
		#1us;
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
	
	`include "spi_frame_macros.sv"
	
	function automatic int get_errors();
		int errors = 0;
		errors += _top_config._check_register_write.get_error_count();
		errors += _top_config._check_elip_command_write.get_error_count();
		for (int channel=0; channel < DSI_CHANNELS; channel++) begin
			errors+=_top_config._check_dsi_command_writes[channel].get_error_count();
		end
		if (!uvm_report_mock::verify_complete()) begin
			errors++;
		end
		return errors;
	endfunction
	
	function automatic void set_channel_bits(spi_command_frame_seq frame, int channels);
		spi_dsi_command_seq	dsi_command;
		foreach (frame.commands[command_index]) begin
			$cast(dsi_command, frame.commands[command_index]);
			dsi_command.channel_bits = channels[1:0];
		end
	endfunction
	
	function automatic void set_pd_cr_flags(spi_command_frame_seq frame, bit pd, bit cr);
		spi_clear_dsi_data_buffers_seq	clear_command;
		foreach (frame.commands[command_index]) begin
			$cast(clear_command, frame.commands[command_index]);
            clear_command.crm_buffer = cr;
            clear_command.pdcm_buffer = pd;
		end
	endfunction
	
	`SVUNIT_TESTS_BEGIN
		enable_clk = 1'b1;
		#10us;
		
		`SVTEST ($sformatf("write register"))
			_frame_facade.start_this(spi_frame_factory::create_frame_with_write_register_commands(null, 1));
			
			#1us;
			`FAIL_UNLESS_EQUAL(get_errors(), 0)
		`SVTEST_END
		
		for (int address=0; address<'h25; address++) begin
			`SVTEST ($sformatf("write register with address=0x%2h", address))
				spi_command_frame_seq frame = new();
				spi_write_master_register_seq seq;
				seq = spi_seq_factory#(spi_write_master_register_seq)::create_seq();
				seq.address = address;
				frame.add_command(seq);
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		repeat(20) begin
			shortint address = $urandom_range(16'h1000, 16'h0400);
			`SVTEST ($sformatf("try write RAM address 0x%4h", address))
				spi_command_frame_seq frame = new();
				spi_write_master_register_seq seq;
				seq = spi_seq_factory#(spi_write_master_register_seq)::create_seq();
				seq.address = address;
				frame.add_command(seq);
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("CRM | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_crm_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("PDCM | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_pdcm_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("WAIT | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_dsi_wait_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("TDMA packet | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_upload_tdma_packet_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("TDMA validate | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_validate_tdma_scheme_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("DM | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_discovery_mode_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("SYNC | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_sync_dsi_channels_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("Clear DSI command queue | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_clear_dsi_command_queue_seq)::create_frame(null);
				set_channel_bits(frame, channels);
				_frame_facade.start_this(frame);
				
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("Clear CRM data buffer | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_clear_dsi_data_buffers_seq)::create_frame(null);
				set_channel_bits(frame, channels);
                set_pd_cr_flags(.frame(frame), .pd(1'b0), .cr(1'b1));
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("Clear PDCM data buffer | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_clear_dsi_data_buffers_seq)::create_frame(null);
				set_channel_bits(frame, channels);
                set_pd_cr_flags(.frame(frame), .pd(1'b1), .cr(1'b0));
				_frame_facade.start_this(frame);
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("Clear DSI data buffer by setting dsi enable to '0' | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_crm_seq)::create_frame(null);
				set_channel_bits(frame, 4'hf);
				_frame_facade.start_this(frame);
				#5us;
				foreach (_top_config._check_dsi_command_writes[i]) begin
					_top_config._check_dsi_command_writes[i].set_enable(~channels[i]);
				end
				dsi3_enabled = ~(dsi_logic_t'(channels));
				#1us;
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		for (int channels=0; channels<(1<<DSI_CHANNELS); channels++) begin
			`SVTEST ($sformatf("Check enable does not transmit commands to channel buffer | channels=%4b", channels))
				spi_command_frame_seq frame = spi_frame_factory_with_single_command #(spi_crm_seq)::create_frame(null);
				foreach (_top_config._check_dsi_command_writes[i]) begin
					_top_config._check_dsi_command_writes[i].set_enable(~channels[i]);
				end
				dsi3_enabled = ~(dsi_logic_t'(channels));
				set_channel_bits(frame, 4'hf);
				_frame_facade.start_this(frame);
				#5us;
				
				dsi3_enabled = '1;
				foreach (_top_config._check_dsi_command_writes[i]) begin
					_top_config._check_dsi_command_writes[i].set_enable(1'b1);
				end
				
				_frame_facade.start_this(frame);
				#5us;
					
				`FAIL_UNLESS_EQUAL(get_errors(), 0)
			`SVTEST_END
		end
		
		enable_clk = 1'b0;
	`SVUNIT_TESTS_END
		
endmodule
