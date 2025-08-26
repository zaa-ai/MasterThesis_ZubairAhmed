/**
 * Module: data_storage
 *
 * Module including RAM for storing all the data
 */
module data_storage import project_pkg::*; (
		clk_reset_if.slave	clk_rst,
		elip_full_if.slave	elip_write_register,
		elip_full_if.slave	elip_spi_command_buffer,
		elip_full_if.slave	elip_dsi_command_buffer[DSI_CHANNELS-1:0],
		elip_full_if.slave	elip_dsi_pdcm_data_buffer[DSI_CHANNELS-1:0],
		elip_full_if.slave	elip_dsi_crm_data_buffer[DSI_CHANNELS-1:0],
		elip_full_if.slave	elip_dsi_tdma[DSI_CHANNELS-1:0],
		elip_full_if.slave	elip_spi_read,
		elip_full_if.slave	elip_jtag,
		elip_full_if.slave	elip_main_fsm,
		elip_if.master		elip_registers,
		jtag_bus_if.slave   jtag_bus,
		ecc_error_if.master	ecc_error,

		output  jtag_dr_for_registers_t       o_jtag_dr,
		input   logic           i_scan_mode,
		input	elip_data_t		i_data_read
	);

	elip_full_if elip_to_ram ();
	elip_full_if elip_ram ();
	elip_full_if elip_2_registers ();

	elip_system_arbiter i_elip_system_arbiter (
			.clk_rst              (clk_rst                ),
			.elip_write_register  (elip_write_register    ),
			.elip_spi_read        (elip_spi_read          ),
			.elip_jtag            (elip_jtag              ),
			.elip_main_fsm        (elip_main_fsm          ),
			.elip_registers       (elip_2_registers.master),
			.elip_ram             (elip_to_ram.master     ));

	elip_full_to_elip i_elip_full_to_elip (
			.elip_full  (elip_2_registers.slave ),
			.elip       (elip_registers         ),
			.i_data_read   (i_data_read         ));

	elip_ram_access_arbiter i_elip_ram_access_arbiter (
			.elip_system              (elip_to_ram.slave        ),
			.elip_spi_command_buffer  (elip_spi_command_buffer  ),
			.elip_dsi_command_buffer  (elip_dsi_command_buffer  ),
			.elip_dsi_pdcm_data_buffer(elip_dsi_pdcm_data_buffer),
			.elip_dsi_crm_data_buffer (elip_dsi_crm_data_buffer ),
			.elip_dsi_tdma            (elip_dsi_tdma            ),
			.elip_ram                 (elip_ram.master          ));

	/*###   RAM wrapper ######################################################*/
	ram_wrapper_ecc_with_bist i_ram_wrapper_ecc_with_bist (
			.clk_rst      (clk_rst               ),
			.elip         (elip_ram.slave        ),
			.jtag_bus     (jtag_bus              ),
			.i_scan_mode  (i_scan_mode           ),
			.o_jtag_dr    (o_jtag_dr             ),
			.ecc_error    (ecc_error             ));

endmodule
