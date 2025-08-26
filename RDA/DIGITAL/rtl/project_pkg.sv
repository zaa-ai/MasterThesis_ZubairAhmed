`ifndef PROJECT_PKG
	`define PROJECT_PKG
	/**
	 * Package: project_pkg
	 *
	 * Project specific things
	 */
	package project_pkg;
		
		localparam	id 						= 32'hE52143;

		`include "base_addresses.sv"
		`include "base_addresses_test.sv"
		`include "register_structs.sv"
		`include "test_register_structs.sv"

		/*###   TIMEBASE   ######################################################*/
		typedef logic[15:0]	timebase_t;

		/*###   ELIP   ######################################################*/
		localparam	DATA_WIDTH = 16;
		localparam  ECC_WIDTH  = 6;
		localparam	ELIP_ADDR_WIDTH = 16;

		typedef logic[DATA_WIDTH-1:0] data_t;
		typedef logic[ECC_WIDTH-1:0]  ecc_t;

		typedef struct packed {
			data_t data; // 16-bit data
			ecc_t  ecc;  // 6-bit  ecc
		} data_ecc_t;

		typedef logic[DATA_WIDTH-1:0] elip_data_t;
		typedef logic[ELIP_ADDR_WIDTH-1:0] elip_addr_t;
		
		/*###   DSI3   ######################################################*/
		localparam DSI_CHANNELS = 2;
		localparam elip_addr_t DSI_CHANNEL_ADDRESS_STEP = 16'h0020;  //TODO: get 'h40 from EDF?!?!
		localparam elip_addr_t DSI_CHANNEL_TRIM_ADDRESS_STEP = 16'h0002;  //TODO: get 'h40 from EDF?!?!
		
		localparam	timebase_t DSI3_TIMING_ERROR_CRM_MIN = timebase_t'(272);
		localparam	timebase_t DSI3_TIMING_ERROR_CRM_MAX = timebase_t'(313);
		localparam	timebase_t DSI3_TIMING_ERROR_CRM_UNCERTAINTY = timebase_t'(3);
		localparam	timebase_t DSI3_TIMING_ERROR_PDCM_MIN = timebase_t'(5);

		/*###   ECC   ######################################################*/
		localparam	ecc_t ECC_FOR_DATA_0 = 6'h0c; // ecc_t'(DWF_ecc_gen_chkbits(16, 6, 16'h0000));
		localparam	ecc_t ECC_FOR_DATA_FFFF = 6'h0c; // ecc_t'(DWF_ecc_gen_chkbits(16, 6, 16'hffff));
        localparam  data_ecc_t  EMPTY_DATA = '{16'd0, ECC_FOR_DATA_0};
		
		/*###   SPI   ######################################################*/
		typedef logic[DSI_CHANNELS:0]	channel_selector_t;
		typedef	logic[DSI_CHANNELS-1:0]	dsi_logic_t;
		typedef	logic[(DSI_CHANNELS*2)-1:0]	buffer_interrupts_t;
		typedef	logic[1:0]	dsi_select_t;	//TODO: make dependent to DSI_CHANNELS

		/*###   JTAG   ######################################################*/
		localparam	JTAG_IR_WIDTH = 8;
		localparam	JTAG_DR_WIDTH = 16;
		typedef logic[JTAG_DR_WIDTH-1:0]	jtag_dr_for_registers_t;
		typedef logic[31:0]	jtag_dr_t;

		/*###   trim   ######################################################*/
		localparam	TRIM_IREF_WIDTH				= 4;
		typedef logic[TRIM_IREF_WIDTH-1:0]		trim_iref_t;
		localparam	TRIM_OSC_F_WIDTH			= 7;
		typedef logic[TRIM_OSC_F_WIDTH-1:0]		trim_osc_f_t;
		localparam	TRIM_OSC_TCF_WIDTH			= 3;
		typedef logic[TRIM_OSC_TCF_WIDTH-1:0]	trim_osc_tcf_t;

		/*###   debounce times   ######################################################*/
		localparam   VCC_UV_DEB_TIME			= 75; // us
		localparam   RESB_DEB_TIME				= 18; // clock cycles
		localparam   OT_DEB_TIME				= 10; // us
		localparam   LDO_UV_DEB_TIME			= 10; // us
		localparam   VRR_DEB_TIME				= 75; // us
		localparam   SYNCB_DEB_TIME				= 10; // clock cycles

		/*###   SRAM   ######################################################*/
		localparam   SRAM_NUM_PARTS             = 1;
		localparam   SRAM_ADDR_WIDTH            = 12;
		localparam   SRAM_WIDTH                 = 23;
		localparam   SRAM_DEPTH                 = 3072;
		localparam   SRAM_WITH_PARITY           = 1'b0;
		localparam   SRAM_WITH_ECC              = 1'b1;
		localparam   SRAM_PROTECT_ADDR          = 1'b1;
		localparam   SRAM_MARCH_17N             = 1'b0; // if 0 MARCH_22n is used

		/*###   TEST   ######################################################*/
		localparam	TMR_OUT_TEST_VECTOR_WIDTH = 59;
		localparam	TMR_OUT_TEST_SEL_WIDHT    = 6;
		typedef	logic[TMR_OUT_TEST_VECTOR_WIDTH-1:0]	tmr_out_test_vector_t;
		typedef	logic[TMR_OUT_TEST_SEL_WIDHT-1:0] 		tmr_out_test_sel_t;
		
	endpackage

`endif
