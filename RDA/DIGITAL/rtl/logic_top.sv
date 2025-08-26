/**
 * Module: logic_top
 *
 * module containing all digital modules e.g. SPI, timebase, main_control, data_storage, buffers, ...
 */
module logic_top import dsi3_pkg::*; import project_pkg::*; (
		input	logic	i_clock_osc,
		input	logic	i_resb,
		input	logic	i_por_n,

		clk_reset_if.master		clk_rst_top, //TODO: bad practice

		spi_int_if.slave 		spi_int,
		jtag_pad_if.slave		jtag,
		dsi3_io_if.master		dsi3_io[DSI_CHANNELS-1:0],
		timebase_io_if.master	timebase_io,
		supply_io_if.master		supply_io,
		otp_io_if.master		otp_io,

		tmr_dsi_if.master		tmr_dsi[DSI_CHANNELS-1:0],
		tmr_out_dsi_if.master	tmr_out_dsi[DSI_CHANNELS-1:0],
		tmr_osc_if.master		tmr_osc,
		tmr_out_osc_if.master	tmr_out_osc,
		tmr_supply_if.master	tmr_supply,
		tmr_out_supply_if.master	tmr_out_supply,
		tmr_scan_if.master		tmr_scan,
		tmr_top_if.master		tmr_top,

		pad_int_if.master		dab_pad,
		pad_int_if.master		bfwb_pad,
		pad_int_if.master		rfc_pad,
		pad_int_if.master		intb_pad,
		pad_int_if.master		syncb_pad,
		output	logic			o_otp_ehv
	);

	/*##############################################################################################*/
	/*###   signal and interface definition   ######################################################*/

	clk_reset_if clk_rst();	//TODO: time consuming
	clk_reset_if clkosc_rst();

	assign	clk_rst_top.clk = clk_rst.clk;
	assign	clk_rst_top.rstn = clk_rst.rstn;

	// ECC interfaces
	ecc_error_if		spi_core_ecc_error(), ram_ecc_error(), spi_cmd_buf_ecc_error(), spi_cmd_ecc_error();
	ecc_error_if#(DSI_CHANNELS)	dsi_cmd_buf_ecc_error(), dsi_crm_data_buf_ecc_error(), dsi_pdcm_data_buf_ecc_error(), dsi_cmd_ecc_error(), dsi_data_ecc_error(), spi_data_ecc_error(), dsi_tdma_ecc_error();

	// buffer interfaces
	buffer_writer_if spi_command_writer();
	buffer_writer_if dsi3_command_writer[DSI_CHANNELS-1:0]();
	buffer_reader_if dsi3_command_reader[DSI_CHANNELS-1:0]();
	buffer_reader_if dsi3_pdcm_data_reader();
    pdcm_buffer_writer_if dsi3_pdcm_data_writer[DSI_CHANNELS-1:0]();
	buffer_reader_if dsi3_crm_data_reader();
	buffer_writer_if dsi3_crm_data_writer[DSI_CHANNELS-1:0]();
	buffer_reader_if command_reader();

	// ELIP interfaces
	elip_full_if elip_spi_command_buffer ();
	elip_full_if elip_write_register ();
	elip_full_if elip_dsi3_command_buffer [DSI_CHANNELS-1:0]();
	elip_full_if elip_dsi3_data_buffer [DSI_CHANNELS-1:0]();
	elip_full_if elip_dsi3_data_crm_buffer [DSI_CHANNELS-1:0]();
	elip_full_if elip_dsi3_tdma [DSI_CHANNELS-1:0]();

	elip_full_if elip_spi_read ();
	elip_full_if elip_jtag ();
	elip_full_if elip_main_fsm ();

	elip_if #(.addr_width  (ELIP_ADDR_WIDTH ), .data_width  (DATA_WIDTH ))  elip_registers ();
	elip_data_t	elip_data_read, elip_time_base_data_read, elip_dsi_data_read, elip_main_control_read, elip_buffers_read;
	elip_data_t	elip_spi_data_read;
	assign	elip_data_read = elip_time_base_data_read | elip_dsi_data_read | elip_main_control_read | elip_buffers_read | elip_spi_data_read;

	dsi_select_t	dsi3_pdcm_data_reader_channel_select;
	dsi_select_t	dsi3_crm_data_reader_channel_select;

	// SPI
	spi_status_if spi_status();

	// main control
	logic	enable_transceivers, overtemperature_switchoff;
	otp_ip_bus_if #(.addr_width  (12 ),	.data_width  (12 )) otp_ip_bus ();
	dsi_logic_t	clear_dsi3_command_buffer, clear_dsi3_crm_data_buffer, clear_dsi3_pdcm_data_buffer;
	logic		clear_spi_command_buffer;
	logic		initializing;
    logic       ram_initialized;
	
	// command control
	logic	clear_spi_command_queue, hw_fail_command_control;
    logic   spi_set_command_ignored;

	// DSI3
	command_control_to_dsi3_if	command_control_to_dsi3 ();
	dsi_logic_t dsi3_transmit_pending;
    data_t      tdma_frame_word_count[DSI_CHANNELS-1:0];

	// timebase
	timebase_info_if timebase_info ();

	// test
	clock_switch_if clock_switch ();
	jtag_dr_for_registers_t	jtag_dr_supply, jtag_dr_osc, jtag_dr, jtag_dr_dsi, jtag_dr_data_storage;
	jtag_bus_if #(.addr_width  (JTAG_IR_WIDTH ), .data_width  (JTAG_DR_WIDTH )) jtag_bus ();
	assign	jtag_dr = jtag_dr_osc | jtag_dr_supply | jtag_dr_dsi | jtag_dr_data_storage;

	/*###################################################################################*/
	/*###   Instances and wiring   ######################################################*/
	dsi_logic_t	dsi_interrupts;
	logic	spi_interrupt, buffer_interrupt;
	
	/*###   main control   ######################################################*/
	main_control #(
		.ADDR_WIDTH           (ELIP_ADDR_WIDTH       )
	) i_main_control (
		.clk_rst                      (clk_rst.slave                    ),
		.elip                         (elip_registers.slave             ),
		.elip_main_fsm                (elip_main_fsm.master             ),
		.supply_io                    (supply_io                        ),
		.time_base                    (timebase_info.slave              ),
		.otp_ip_bus                   (otp_ip_bus.master                ),
		.rfc_pad                      (rfc_pad                          ),
		.intb_pad                     (intb_pad                         ),
		.jtag_bus                     (jtag_bus.slave                   ),
		.tmr_supply                   (tmr_supply                       ),
		.tmr_out_supply               (tmr_out_supply                   ),
		.i_dsi_interrupts             (dsi_interrupts                   ),
		.i_spi_interrupt              (spi_interrupt                    ),
		.i_buffer_interrupt           (buffer_interrupt                 ),
		.i_command_control_hw_fail    (hw_fail_command_control          ),
		.o_temp_error                 (                                 ),
		.o_overtemperature_switchoff  (overtemperature_switchoff        ),
		.o_elip_out                   (elip_main_control_read           ),
		.o_enable_transceivers        (enable_transceivers              ),
		.o_otp_ehv                    (o_otp_ehv                        ),
		.o_jtag_dr                    (jtag_dr_supply                   ),
		.o_clear_dsi3_command_buffer  (clear_dsi3_command_buffer        ),
		.o_clear_dsi3_crm_data_buffer (clear_dsi3_crm_data_buffer       ),
		.o_clear_dsi3_pdcm_data_buffer(clear_dsi3_pdcm_data_buffer      ),
		.o_clear_spi_command_buffer   (clear_spi_command_buffer         ),
		.o_initializing               (initializing                     ),
        .o_ram_initialized            (ram_initialized                  ),
		
		.spi_cmd_ecc_error            (spi_cmd_ecc_error.slave          ),
		.spi_data_ecc_error           (spi_data_ecc_error.slave         ),
		.spi_cmd_buf_ecc_error        (spi_cmd_buf_ecc_error.slave      ),
		.spi_core_ecc_error           (spi_core_ecc_error.slave         ),
		.ram_ecc_error                (ram_ecc_error.slave              ),
		.dsi3_cmd_buf_ecc_error       (dsi_cmd_buf_ecc_error.slave      ),
		.dsi3_crm_data_buf_ecc_error  (dsi_crm_data_buf_ecc_error.slave ),
		.dsi3_pdcm_data_buf_ecc_error (dsi_pdcm_data_buf_ecc_error.slave),
		.dsi3_cmd_ecc_error           (dsi_cmd_ecc_error.slave          ),
		.dsi3_data_ecc_error          (dsi_data_ecc_error.slave         ),
        .dsi3_tdma_ecc_error          (dsi_tdma_ecc_error.slave         ),
		.spi_status                   (spi_status.main_control          ));

	/*###   Buffer   ######################################################*/
	buffers #(
			.ADDR_WIDTH                (ELIP_ADDR_WIDTH                )
		) i_buffers (
			.clk_rst                   (clk_rst.slave                   ),
			.command_reader            (command_reader.slave            ),
			.command_writer            (spi_command_writer.slave        ),
			.dsi3_command_reader       (dsi3_command_reader.slave       ),
			.dsi3_command_writer       (dsi3_command_writer.slave       ),
			.dsi3_pdcm_data_reader     (dsi3_pdcm_data_reader.slave     ),
			.dsi3_pdcm_data_writer     (dsi3_pdcm_data_writer.slave     ),
			.dsi3_crm_data_reader      (dsi3_crm_data_reader.slave      ),
			.dsi3_crm_data_writer      (dsi3_crm_data_writer.slave      ),
			.elip_command_buffer       (elip_spi_command_buffer.master  ),
			.elip_dsi3_command_buffer  (elip_dsi3_command_buffer.master ),
			.elip_dsi3_pdcm_data_buffer(elip_dsi3_data_buffer.master    ),
			.elip_dsi3_crm_data_buffer (elip_dsi3_data_crm_buffer.master),
			.elip_registers            (elip_registers.slave            ),
			.i_dsi3_pdcm_data_reader_channel_select(dsi3_pdcm_data_reader_channel_select),
			.i_dsi3_crm_data_reader_channel_select(dsi3_crm_data_reader_channel_select),
			.o_elip_registers_data_out (elip_buffers_read               ),
			.o_interrupt               (buffer_interrupt                ),
			.dab_pad                   (dab_pad                         ),
			.bfwb_pad                  (bfwb_pad                        ),
			.o_dsi3_pdcm_data_available(spi_status.dsi3_pdcm_data_available  ),
			.o_dsi3_crm_data_available (spi_status.dsi3_crm_data_available       ),
			.o_buffer_fill_warning     (spi_status.buffer_fill_warning  ),
			.spi_cmd_buf_ecc_error     (spi_cmd_buf_ecc_error.master    ),
			.dsi_cmd_buf_ecc_error     (dsi_cmd_buf_ecc_error.master    ),
			.dsi_crm_data_buf_ecc_error(dsi_crm_data_buf_ecc_error.master   ),
			.dsi_pdcm_data_buf_ecc_error(dsi_pdcm_data_buf_ecc_error.master   ));

	/*###   SPI   ######################################################*/
	spi i_spi (
			.clk_rst                 (clk_rst.slave               ),
			.spi_int                 (spi_int                     ),
			.elip_spi_read           (elip_spi_read.master        ),
			.command_writer          (spi_command_writer.master   ),
			.dsi3_pdcm_data_reader   (dsi3_pdcm_data_reader.master),
			.dsi3_crm_data_reader    (dsi3_crm_data_reader.master ),
			.spi_status              (spi_status.spi              ),
			.elip_registers          (elip_registers.slave        ),
			.spi_ecc_error           (spi_core_ecc_error.master   ),
			.data_reader_ecc_error   (spi_data_ecc_error.master   ),
			.i_clear_command_queue   (clear_spi_command_queue | clear_spi_command_buffer),
            .i_tdma_frame_word_count (tdma_frame_word_count       ),
			.i_write_not_allowed     (initializing                ),
            .i_ram_initialized       (ram_initialized             ),
            .i_set_command_ignored   (spi_set_command_ignored     ),
			.o_elip_data_read        (elip_spi_data_read          ),
			.o_interrupt             (spi_interrupt               ),
			.o_dsi3_pdcm_data_read_channel_select(dsi3_pdcm_data_reader_channel_select),
			.o_dsi3_crm_data_read_channel_select(dsi3_crm_data_reader_channel_select)
	);

	/*###   command control   ######################################################*/
	command_control i_command_control (
			.clk_rst              (clk_rst.slave                 ),
			.elip_write_register  (elip_write_register.master    ),
			.command_reader       (command_reader.master         ),
			.dsi_command_writer   (dsi3_command_writer.master    ),
			.to_dsi3              (command_control_to_dsi3.master),
			.ecc_error            (spi_cmd_ecc_error.master      ),
			.i_clear_dsi3_command_queue(clear_dsi3_command_buffer),
			.o_hw_fail            (hw_fail_command_control       ),
			.o_clear_command_queue(clear_spi_command_queue       ),
            .o_set_command_ignored(spi_set_command_ignored       ));

	/*###   data storage (RAM etc)   ######################################################*/
	data_storage i_data_storage (
			.clk_rst                  (clk_rst.slave                 ),
			.elip_write_register      (elip_write_register.slave     ),
			.elip_spi_command_buffer  (elip_spi_command_buffer.slave ),
			.elip_dsi_command_buffer  (elip_dsi3_command_buffer.slave),
			.elip_dsi_pdcm_data_buffer(elip_dsi3_data_buffer.slave   ),
			.elip_dsi_crm_data_buffer (elip_dsi3_data_crm_buffer.slave   ),
			.elip_dsi_tdma            (elip_dsi3_tdma.slave          ),
			.elip_spi_read            (elip_spi_read.slave           ),
			.elip_jtag                (elip_jtag.slave               ),
			.elip_main_fsm            (elip_main_fsm.slave           ),
			.elip_registers           (elip_registers.master         ),
			.jtag_bus                 (jtag_bus.slave                ),
			.o_jtag_dr                (jtag_dr_data_storage          ),
			.i_scan_mode              (tmr_scan.scan                 ),
			.i_data_read              (elip_data_read                ),
			.ecc_error                (ram_ecc_error.master          ));

	/*###   DSI3 cores   ######################################################*/
	dsi3 #(.ADDR_WIDTH                         (16                        )
		) i_dsi3 (
			.clk_rst                            (clk_rst.slave                     ),
			.command_reader                     (dsi3_command_reader.master        ),
			.elip_registers                     (elip_registers.slave              ),
			.elip_tdma							(elip_dsi3_tdma.master             ),
			.o_elip_data_read                   (elip_dsi_data_read                ),
			.pdcm_data_writer                   (dsi3_pdcm_data_writer.master      ),
			.crm_data_writer                    (dsi3_crm_data_writer.master       ),
			.dsi3_io                            (dsi3_io                           ),
			.time_base                          (timebase_info.slave               ),
			.syncb_pad                          (syncb_pad                         ),
			.from_command_control               (command_control_to_dsi3.slave     ),
			.ecc_error_cmd                      (dsi_cmd_ecc_error.master          ),
			.ecc_error_data                     (dsi_data_ecc_error.master         ),
            .ecc_error_tdma                     (dsi_tdma_ecc_error.master         ),
			.jtag_bus                           (jtag_bus.slave                    ),
			.tmr_dsi                            (tmr_dsi                           ),
			.tmr_out_dsi                        (tmr_out_dsi                       ),
			.i_ot                               (overtemperature_switchoff         ),
			.i_vdsi_en                          (supply_io.ldo_en                  ),
			.i_enable_transceivers              (enable_transceivers               ),
			.i_clear_crm_data_buffer            (clear_dsi3_crm_data_buffer        ),
			.i_clear_pdcm_data_buffer           (clear_dsi3_pdcm_data_buffer       ),
            .i_invalidate_tdma_schemes          (ram_ecc_error.double_error        ),
			.o_interrupt                        (dsi_interrupts                    ),
			.o_transmit_pending                 (dsi3_transmit_pending             ),
			.o_hardware_error                   (spi_status.dsi3_hardware_error    ),
			.o_jtag_dr                          (jtag_dr_dsi                       ),
			.o_hw_fail                          (spi_status.hardware_fail_dsi3     ),
			.o_no_tdma_scheme_defined           (spi_status.no_tdma_scheme_defined ),
            .o_tdma_frame_word_count            (tdma_frame_word_count             )
        );

	/*###   time base   ######################################################*/
	timebase #(
			.base_addr                   (BASE_ADDR_TIMEBASE         ),
			.addr_width                  (16		                 ),
			.DSI3_COUNT                  (DSI_CHANNELS               )
		) i_timebase (
			.clk_rst                     (clk_rst.slave              ),
			.clkosc_rst                  (clkosc_rst.slave           ),
			.timebase_info               (timebase_info.master       ),
			.timebase_io                 (timebase_io                ),
			.clock_switch_io             (clock_switch.timebase      ),
			.tmr_osc                     (tmr_osc                    ),
			.tmr_out_osc                 (tmr_out_osc                ),
			.jtag_bus                    (jtag_bus.slave             ),
			.o_jtag_dr                   (jtag_dr_osc                ),
			.i_scanmode                  (tmr_scan.scan              ),
			.elip                        (elip_registers.slave       ),
			.o_elip_data_read            (elip_time_base_data_read   ),
			.i_transmit_pending          (dsi3_transmit_pending      )
		);
	assign	spi_status.clkref_failure = ~timebase_info.clkref_ok;

	/*###   test   ######################################################*/
	assign	clock_switch.clock_osc = i_clock_osc;
	assign	clock_switch.clock_pll = timebase_io.clkpll; //TODO: time consuming

	test i_test (
			.clk_rst         (clk_rst.master      ),
			.clkosc_rst      (clkosc_rst.master   ),
			.otp_io          (otp_io              ),
			.otp_ip_bus      (otp_ip_bus.slave    ),
			.clock_switch_io (clock_switch.slave  ),
			.tmr_top         (tmr_top             ),
			.jtag            (jtag                ),
			.jtag_bus        (jtag_bus.master     ),
			.i_jtag_dr       (jtag_dr             ),
			.tmr_scan        (tmr_scan            ),
			.elip            (elip_jtag.master    ),
			.i_porb          (i_por_n             ),
			.i_resb          (i_resb              ));

endmodule


