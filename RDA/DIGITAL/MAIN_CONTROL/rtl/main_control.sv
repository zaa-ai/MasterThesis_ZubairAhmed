`include "global_defines.sv"
/**
 * Module: main_control
 *
 * module for controlling main features like interrupts and so on
 * 
 */
module main_control import project_pkg::*; #(
		parameter ADDR_WIDTH = 16
	)(
		clk_reset_if.slave		clk_rst,
		elip_if.slave			elip,
		supply_io_if.master		supply_io,
		timebase_info_if.slave	time_base,
		otp_ip_bus_if.master	otp_ip_bus,
		elip_full_if.master 	elip_main_fsm,
		pad_int_if.master		rfc_pad,
		pad_int_if.master		intb_pad,
		
		// ECC
		ecc_error_if.slave		spi_cmd_ecc_error,
		ecc_error_if.slave		spi_data_ecc_error,
		ecc_error_if.slave		spi_core_ecc_error,
		ecc_error_if.slave		spi_cmd_buf_ecc_error,
		ecc_error_if.slave		ram_ecc_error,
		
		ecc_error_if.slave		dsi3_cmd_buf_ecc_error,
		ecc_error_if.slave		dsi3_crm_data_buf_ecc_error,
		ecc_error_if.slave		dsi3_pdcm_data_buf_ecc_error,
		ecc_error_if.slave		dsi3_cmd_ecc_error,
		ecc_error_if.slave		dsi3_data_ecc_error,
		ecc_error_if.slave		dsi3_tdma_ecc_error,

		// test
		tmr_supply_if.master	tmr_supply,
		tmr_out_supply_if.master	tmr_out_supply,
		jtag_bus_if.slave		jtag_bus,
		output	jtag_dr_for_registers_t	o_jtag_dr,

		input	dsi_logic_t		i_dsi_interrupts,
		input	logic			i_spi_interrupt,
		input	logic			i_buffer_interrupt, // 1 Command queue + (1 data buffer + 1 Command queue) in DSIs
		input	logic			i_command_control_hw_fail,
		output	logic			o_temp_error,
		output	logic			o_overtemperature_switchoff,
		output	elip_data_t		o_elip_out,
		output	logic			o_enable_transceivers,
		output	logic			o_otp_ehv,
		spi_status_if.main_control	spi_status,
		output	dsi_logic_t		o_clear_dsi3_crm_data_buffer,
		output	dsi_logic_t		o_clear_dsi3_pdcm_data_buffer,
		output	dsi_logic_t		o_clear_dsi3_command_buffer,
		output	logic			o_clear_spi_command_buffer,
		output	logic			o_initializing,
        output  logic           o_ram_initialized
	);

	elip_data_t	elip_out_ic_revision, elip_out_supply, elip_out_interrupt, elip_out_main_fsm;
	assign	o_elip_out = elip_out_ic_revision | elip_out_supply | elip_out_interrupt | elip_out_main_fsm;
	
	logic	rfc;
	logic	temp_warn, temp_error, ldo_ok_sync, ldo_ok_deb;
	logic	prevent_overtemperature_switch_off, prevent_overtemperature_switch_off_sync;
	logic	enable_ldo;
	
	logic	vrr_ok_sync, vrr_ok_deb;
	logic	main_fsm_fail;
	ecc_error_if #(.WIDTH (1)) ecc_error ();

	/*###   IC revision & ID   ######################################################*/
	`include "IC_revision_and_ID_registers_if_inst.sv"
	`include "supply_registers_if_inst.sv"
	`include "Interrupt_Registers_if_inst.sv"
	
	IC_revision_and_ID_registers #(
			.base_addr                                  (BASE_ADDR_INFO                            ),
			.addr_width                                 (ADDR_WIDTH                                )
		) i_IC_revision_and_ID_registers (
			.clk_rst                                    (clk_rst                                   ),
			.addr                                       (elip.addr                                 ),
			.data_in                                    (elip.data_write                           ),
			.wr                                         (elip.wr                                   ),
			.rd                                         (elip.rd                                   ),
			.data_out                                   (elip_out_ic_revision                      ),
			.IC_revision_and_ID_registers_IC_REVISION   (IC_revision_and_ID_registers_IC_REVISION.master  ),
			.IC_revision_and_ID_registers_CHIP_ID_LOW   (IC_revision_and_ID_registers_CHIP_ID_LOW.master  ),
			.IC_revision_and_ID_registers_CHIP_ID_HIGH  (IC_revision_and_ID_registers_CHIP_ID_HIGH.master ));
	
	ic_revision i_ic_revision (.o_ic_revision (IC_revision_and_ID_registers_IC_REVISION.REVISION_in));

	/*###   supply sync & debounce   ######################################################*/
	assign	o_temp_error = temp_error;

	sync_deb_long #(
			.DEBOUNCE_TIME    (project_pkg::OT_DEB_TIME   ),
			.RESET_VALUE      (1'b0     )
		) i_sync_deb_ot_warn (
			.clk_rst          (clk_rst        ),
			.i_in             (supply_io.temp_warn),
			.i_debounce_tick  (time_base.tick_1us),
			.o_out            (temp_warn      ),
			.o_out_synced     (               ),
			.o_test_out       (tmr_out_supply.ot_warning_synced)
		);

	sync_deb_long #(
			.DEBOUNCE_TIME    (project_pkg::OT_DEB_TIME   ),
			.RESET_VALUE      (1'b0     )
		) i_sync_deb_ot_error (
			.clk_rst          (clk_rst        ),
			.i_in             (supply_io.temp_error),
			.i_debounce_tick  (time_base.tick_1us),
			.o_out            (temp_error     ),
			.o_out_synced     (      ),
			.o_test_out       (tmr_out_supply.ot_error_synced  )
		);

	sync_deb_long #(
			.DEBOUNCE_TIME    (project_pkg::LDO_UV_DEB_TIME   ),
			.RESET_VALUE      (1'b0     )
		) i_sync_deb_ldo_ok (
			.clk_rst          (clk_rst         ),
			.i_in             (supply_io.ldo_ok            ),
			.i_debounce_tick  (time_base.tick_1us ),
			.o_out            (ldo_ok_deb           ),
			.o_out_synced     (ldo_ok_sync    ),
			.o_test_out       (tmr_out_supply.ldo_ok_synced     ));

	logic	vcc_ok_sync, vcc_ok_deb, vcc_ok_for_otp;
	sync_deb_long #(
			.DEBOUNCE_TIME    (project_pkg::VCC_UV_DEB_TIME   ),
			.RESET_VALUE      (1'b1     )
		) i_sync_deb_long_vccok (
			.clk_rst          (clk_rst            ),
			.i_in             (supply_io.vcc_ok   ),
			.i_debounce_tick  (time_base.tick_1us ),
			.o_out            (vcc_ok_deb         ),
			.o_out_synced     (vcc_ok_sync        ),
			.o_test_out       (tmr_out_supply.vcc_ok_synced));
	
	vcc_deb #(
		.DEBOUNCE_TIME    (project_pkg::VCC_UV_DEB_TIME   ), 
		.RESET_VALUE      (1'b0               )
	) i_vcc_deb_for_otp (
		.clk_rst          (clk_rst            ), 
		.i_in             (vcc_ok_sync        ), 
		.i_debounce_tick  (time_base.tick_1us ), 
		.o_out            (vcc_ok_for_otp     ));
	
	sync_deb_long #(
		.DEBOUNCE_TIME    (project_pkg::VRR_DEB_TIME   ), 
		.RESET_VALUE      (1'b0     )
		) i_sync_deb_long_vrr_ok (
		.clk_rst          (clk_rst         ), 
		.i_in             (supply_io.vrr_ok), 
		.i_debounce_tick  (time_base.tick_1us ), 
		.o_out            (vrr_ok_deb      ), 
		.o_out_synced     (vrr_ok_sync     ),
		.o_test_out       (tmr_out_supply.vrr_ok_synced      ));
	
	assign	spi_status.vcc_uv = ~vcc_ok_sync;
	assign	spi_status.ldo_uv = ~ldo_ok_deb;
	assign	spi_status.vrr_nok = ~vrr_ok_deb;
	assign	spi_status.overtemperature = temp_warn;
	assign	spi_status.ecc_failure = |(Interrupt_Registers_ECC_IRQ_STAT.value);
	assign	spi_status.otp_fail = Interrupt_Registers_IRQ_STAT.OTPFAIL;

	/*###   supply registers   ######################################################*/
	supply_registers #(
			.base_addr                     (BASE_ADDR_SUPPLY             ),
			.addr_width                    (ADDR_WIDTH                   )
		) i_supply_registers (
			.clk_rst                       (clk_rst                      ),
			.addr                          (elip.addr                    ),
			.data_in                       (elip.data_write              ),
			.wr                            (elip.wr                      ),
			.rd                            (elip.rd                      ),
			.data_out                      (elip_out_supply              ),
			.supply_registers_SUP_STAT     (supply_registers_SUP_STAT.master    ),
			.supply_registers_SUP_CTRL     (supply_registers_SUP_CTRL.master    ),
			.supply_registers_SUP_HW_CTRL  (supply_registers_SUP_HW_CTRL.master ),
			.supply_registers_IO_CTRL      (supply_registers_IO_CTRL.master     ),
			.supply_registers_TRIM_IREF    (supply_registers_TRIM_IREF.master   ),
			.supply_registers_TRIM_OT      (supply_registers_TRIM_OT.master     ),
			.supply_registers_SUP_IRQ_STAT (supply_registers_SUP_IRQ_STAT.master),
			.supply_registers_SUP_IRQ_MASK (supply_registers_SUP_IRQ_MASK.master));
	
	logic	supply_interrupt;
	assign	supply_interrupt = |(supply_registers_SUP_IRQ_STAT.value & supply_registers_SUP_IRQ_MASK.value);

	assign	supply_io.trim_iref = supply_registers_TRIM_IREF.IREF;
	assign	supply_io.pad_drive_strength = supply_registers_IO_CTRL.HICUR;
	assign	supply_registers_SUP_STAT.OTE_in = temp_error;
	assign	supply_registers_SUP_STAT.OTW_in = temp_warn;
	assign	supply_registers_SUP_STAT.LDOUV_in = ~ldo_ok_sync;
	assign	supply_registers_SUP_STAT.VCCUV_in = ~vcc_ok_sync;
	assign	supply_registers_SUP_STAT.REF_FAIL_in = ~vrr_ok_sync;
	assign	supply_io.ldo_en = supply_registers_SUP_CTRL.EN_LDO & enable_ldo;
	assign	supply_registers_SUP_CTRL.EN_LDO_set = o_overtemperature_switchoff;
	assign	supply_registers_SUP_CTRL.EN_LDO_in = 1'b0;
	
	assign	supply_registers_SUP_IRQ_STAT.LDOUV_in = 1'b1;
	assign	supply_registers_SUP_IRQ_STAT.OTE_in = 1'b1;
	assign	supply_registers_SUP_IRQ_STAT.OTW_in = 1'b1;
	assign	supply_registers_SUP_IRQ_STAT.REF_FAIL_in = 1'b1;
	assign	supply_registers_SUP_IRQ_STAT.VCCUV_in = 1'b1;
	
	assign	supply_registers_SUP_IRQ_STAT.LDOUV_set = ((~ldo_ok_deb) & rfc);
	assign	supply_registers_SUP_IRQ_STAT.OTE_set = temp_error;
	assign	supply_registers_SUP_IRQ_STAT.OTW_set = temp_warn;
	assign	supply_registers_SUP_IRQ_STAT.REF_FAIL_set = (~vrr_ok_deb) & rfc;
	assign	supply_registers_SUP_IRQ_STAT.VCCUV_set = ((~vcc_ok_deb) & rfc);

	assign	supply_io.trim_ot = supply_registers_TRIM_OT.TRIM_OT;

	/*###   Interrupt registers   ######################################################*/
	Interrupt_Registers #(
			.base_addr                     (BASE_ADDR_INTERRUPT          ),
			.addr_width                    (ADDR_WIDTH                   )
		) i_Interrupt_Registers (
			.clk_rst                       (clk_rst                      ),
			.addr                          (elip.addr                    ),
			.data_in                       (elip.data_write              ),
			.wr                            (elip.wr                      ),
			.rd                            (elip.rd                      ),
			.data_out                      (elip_out_interrupt           ),
			.Interrupt_Registers_IRQ_STAT  (Interrupt_Registers_IRQ_STAT.master ),
			.Interrupt_Registers_IRQ_MASK  (Interrupt_Registers_IRQ_MASK.master ),
		    .Interrupt_Registers_ECC_IRQ_STAT       (Interrupt_Registers_ECC_IRQ_STAT.master      ), 
		    .Interrupt_Registers_ECC_IRQ_MASK       (Interrupt_Registers_ECC_IRQ_MASK.master      ), 
		    .Interrupt_Registers_ECC_CORR_IRQ_STAT  (Interrupt_Registers_ECC_CORR_IRQ_STAT.master ), 
		    .Interrupt_Registers_ECC_CORR_IRQ_MASK  (Interrupt_Registers_ECC_CORR_IRQ_MASK.master ));

	`define Interrupt_Register_IRQ_STAT_set(_field_, _value_) assign	Interrupt_Registers_IRQ_STAT.``_field_``_set = _value_;
	`define Interrupt_Register_IRQ_STAT_in(_field_, _value_) assign	Interrupt_Registers_IRQ_STAT.``_field_``_in = _value_;

	`Interrupt_Register_IRQ_STAT_set (OTPFAIL, ecc_error.double_error)	
	`Interrupt_Register_IRQ_STAT_in  (OTPFAIL, 1'b1)

	`Interrupt_Register_IRQ_STAT_in  (DSI, i_dsi_interrupts)
	`Interrupt_Register_IRQ_STAT_in  (BUF, i_buffer_interrupt)

	`Interrupt_Register_IRQ_STAT_in  (SUPPLY, supply_interrupt)
	`Interrupt_Register_IRQ_STAT_in  (SPI, i_spi_interrupt)

	`Interrupt_Register_IRQ_STAT_set (HW_FAIL, main_fsm_fail | i_command_control_hw_fail)
	`Interrupt_Register_IRQ_STAT_in  (HW_FAIL, 1'b1)


	`Interrupt_Register_IRQ_STAT_set (CLKREF, (~time_base.clkref_ok) & rfc)
	`Interrupt_Register_IRQ_STAT_in  (CLKREF, 1'b1)
	
	assign	spi_status.hardware_fail_main_control = Interrupt_Registers_IRQ_STAT.HW_FAIL;
	
	logic	ecc_irq, ecc_corr_irq;
	assign	ecc_irq	= |(Interrupt_Registers_ECC_IRQ_STAT.value & Interrupt_Registers_ECC_IRQ_MASK.value);
	assign	ecc_corr_irq = |(Interrupt_Registers_ECC_CORR_IRQ_STAT.value & Interrupt_Registers_ECC_CORR_IRQ_MASK.value);
	assign	Interrupt_Registers_IRQ_STAT.ECC_FAIL_in = ecc_irq;
	assign	Interrupt_Registers_IRQ_STAT.RESERVED_in = ecc_corr_irq;
	
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF_in = Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF | dsi3_cmd_buf_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF_in = Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF | dsi3_crm_data_buf_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF_in = Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF | dsi3_pdcm_data_buf_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_in = Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD | dsi3_cmd_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA_in = Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA | dsi3_tdma_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.RAM_in = 1'b1;
	assign	Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF_in = 1'b1;
	assign	Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_in = 1'b1;
	assign	Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA_in = 1'b1;
	
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF_set = |(dsi3_cmd_buf_ecc_error.double_error);
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF_set = |(dsi3_crm_data_buf_ecc_error.double_error);
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF_set = |(dsi3_pdcm_data_buf_ecc_error.double_error);
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_set = |(dsi3_cmd_ecc_error.double_error);
	assign	Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA_set = |(dsi3_tdma_ecc_error.double_error);
	assign	Interrupt_Registers_ECC_IRQ_STAT.RAM_set = ram_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF_set = spi_cmd_buf_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_set = spi_cmd_ecc_error.double_error;
	assign	Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA_set = (|(spi_data_ecc_error.double_error)) | (|(dsi3_data_ecc_error.double_error)) | spi_core_ecc_error.double_error;
	
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF_in = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF | dsi3_cmd_buf_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF_in = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF | dsi3_crm_data_buf_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF_in = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF | dsi3_pdcm_data_buf_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_in = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD | dsi3_cmd_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA_in = Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA | dsi3_tdma_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM_in = 1'b1;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF_in = 1'b1;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_in = 1'b1;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA_in = 1'b1;
    
	
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF_set = |(dsi3_cmd_buf_ecc_error.single_error);
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF_set = |(dsi3_crm_data_buf_ecc_error.single_error);
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF_set = |(dsi3_pdcm_data_buf_ecc_error.single_error);
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_set = |(dsi3_cmd_ecc_error.single_error);
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA_set = |(dsi3_tdma_ecc_error.single_error);
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM_set = ram_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF_set = spi_cmd_buf_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_set = spi_cmd_ecc_error.single_error;
	assign	Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA_set = (|(spi_data_ecc_error.single_error)) | (|(dsi3_data_ecc_error.single_error)) | spi_core_ecc_error.single_error;
    
	
	// collect errors to clear buffers and stop command execution
	assign	o_clear_dsi3_command_buffer = dsi3_cmd_buf_ecc_error.double_error | dsi3_cmd_ecc_error.double_error | {DSI_CHANNELS{ram_ecc_error.double_error}};
	assign	o_clear_dsi3_crm_data_buffer = dsi3_crm_data_buf_ecc_error.double_error | dsi3_data_ecc_error.double_error | spi_data_ecc_error.double_error | {DSI_CHANNELS{ram_ecc_error.double_error}};
	assign	o_clear_dsi3_pdcm_data_buffer = dsi3_pdcm_data_buf_ecc_error.double_error | dsi3_data_ecc_error.double_error | spi_data_ecc_error.double_error | {DSI_CHANNELS{ram_ecc_error.double_error}};
	assign	o_clear_spi_command_buffer = spi_cmd_buf_ecc_error.double_error | spi_cmd_ecc_error.double_error | ram_ecc_error.double_error;
	
	/*###   main FSM   ######################################################*/
	main_fsm i_main_fsm (
		.clk_rst                (clk_rst               ),
		.otp_ip_bus             (otp_ip_bus            ),
		.elip                   (elip_main_fsm         ),
		.elip_registers         (elip                  ),
		.i_vcc_ok               (vcc_ok_for_otp        ),
		.i_vrr_ok               (vrr_ok_deb            ),
		.i_ldo_ok               (ldo_ok_deb            ),
		.i_ignore_ldo_uv        (supply_registers_SUP_HW_CTRL.IGNORE_UV),
		.i_ignore_hwf           (supply_registers_SUP_HW_CTRL.IGNORE_HWF),
		.i_tick_1us             (time_base.tick_1us    ),
		.o_enable_transceivers  (o_enable_transceivers ),
		.o_rfc                  (rfc                   ),
		.o_otp_ehv              (o_otp_ehv             ),
		.o_enable_ldo           (enable_ldo            ),
		.ecc_error              (ecc_error.master      ),
		.o_main_fsm_fail        (main_fsm_fail         ),
		.o_elip_out             (elip_out_main_fsm     ),
		.o_initializing         (o_initializing        ),
        .o_ram_initialized      (o_ram_initialized     )
	);

	/*###   pads   ######################################################*/
	logic	intb, intb_next;
	`PAD_INST(rfc_pad, 1'b1, rfc, 1'b0, 1'b0, 1'b1)
	`PAD_INST(intb_pad, ~intb, intb, 1'b0, 1'b1, 1'b0)

	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin // pad outputs should be FFs -> no glitches
		if (clk_rst.rstn == 1'b0) begin
			intb <= 1'b0;
		end
		else begin
			intb <= intb_next;
		end
	end

	assign	intb_next = ~(|(Interrupt_Registers_IRQ_STAT.value & Interrupt_Registers_IRQ_MASK.value));

	/*###   test   ######################################################*/
	test_supply #(
			.BASE_ADDR                                     (BASE_ADDR_TEST_SUP                  ),
			.ADDR_WIDTH                                    (JTAG_IR_WIDTH                       )
		) i_test_supply (
			.jtag_bus                                      (jtag_bus                            ),
			.o_jtag_dr                                     (o_jtag_dr                           ),
			.tmr_supply                                    (tmr_supply                          ),
			.o_tmr_dig_PREVENT_OVERTEMPERATURE_SWITCH_OFF  (prevent_overtemperature_switch_off  ));
	
	sync i_sync_prevent_ot_switch_off (
		.clk_rst     (clk_rst    ), 
		.i_in        (prevent_overtemperature_switch_off       ), 
		.o_test_out  ( ), 
		.o_out       (prevent_overtemperature_switch_off_sync      ));

	assign	o_overtemperature_switchoff = temp_error & ~prevent_overtemperature_switch_off_sync;
	
	assign	tmr_out_supply.ldo_ok = supply_io.ldo_ok;
	assign	tmr_out_supply.vcc_ok = supply_io.vcc_ok;
	assign	tmr_out_supply.vrr_ok = supply_io.vrr_ok;
	assign	tmr_out_supply.ot_error = supply_io.temp_error;
	assign	tmr_out_supply.ot_warning = supply_io.temp_warn;

endmodule
