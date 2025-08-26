`timescale 1ns/1ns

`ifdef VCS
	`undef VCS
`endif
module fpga import project_pkg::*; #(
        parameter   DSI3_TX_DAC_WIDTH = 5,
        parameter   DSI3_TX_TBIT_CFG_WIDTH = 2,
        parameter   DSI3_RX_TRIM_WIDTH = 4,
        parameter   TRIM_IREF_WIDTH         = 4,
        parameter   TRIM_OSC_F_WIDTH        = 7,
        parameter   TRIM_OSC_TCF_WIDTH      = 3,
        parameter   DSI3_COUNT = DSI_CHANNELS,
        parameter   DSI3_ATST_TX_WIDTH = 7,
        parameter   DSI3_ATST_RX_WIDTH = 2,
        parameter   VDSI_CTRL_WIDTH = 3
		)(
			// ==== clocks ====
			input  logic       CLK_100,
			output logic [2:0] SYS_LED,

			// ==== BUTTON 0..3
			input logic  [3:0]  BUTTON,

			// ==== SWITCH ====
			input logic [4:1]   SW,

			// ==== DBG[0..7] & DBG[8..15] used for verification Hardware of Mariusz and Benjamin H. ====
			output logic  DBG_0,
			output logic  DBG_1,
			input logic  DBG_2,
			input logic  DBG_3,
			input logic  DBG_4,
			input logic  DBG_5,
			input logic  DBG_6,
			input logic  DBG_7,
			output logic  DBG_8,
			output logic  DBG_9,
			output logic  DBG_10,
			output logic  DBG_11,
			inout logic  DBG_12,
			output logic  DBG_13,
			output logic  DBG_14,
			input logic  DBG_15,

			// ==== DSI SUPPLY Switcht ====
			output logic        DSI_SUPPLY_OFF_1_TO_6_FPGA,
			output logic        DSI_SUPPLY_OFF_7_TO_12_FPGA,

			// ==== DUT RESET ====
			input logic         DUT_RESET,

			// ==== LED ====
			input  logic [7:0]  LED,

			// ==== MAZ JTAG BOX ====
			input logic         MAZ_JTAG_DBGRQ_GPIO02,
			input logic         MAZ_JTAG_NTRST,
			input logic         MAZ_JTAG_RTCK_GPIO01,
			input logic         MAZ_JTAG_STRST,
			input logic         MAZ_JTAG_TCK,
			input logic         MAZ_JTAG_TDI_TDA,
			output logic        MAZ_JTAG_TDO,
			input logic         MAZ_JTAG_TMS,

			// ==== DSI Node 1 ====
			output logic        NODE1_CLKREF,
			input  logic        NODE1_CSB,
			input  logic        NODE1_SCK,
			input  logic        NODE1_MISO,
			input  logic        NODE1_MOSI,
			output logic        NODE1_RESB,
			output logic        NODE1_DCR1B, //TDI
			output logic        NODE1_DCR2B, //TCK
			input  logic        NODE1_INTB,  // TDO
			output logic        NODE1_RFC,   //TMS
			output logic        NODE1_TESTMODE,
			output logic        NODE1_DSI_OFF,
			output logic [4:0]  NODE1_DBG,

			// ==== DSI Node 2 ====
			output logic        NODE2_CLKREF,
			input  logic        NODE2_CSB,
			input  logic        NODE2_SCK,
			input  logic        NODE2_MISO,
			input  logic        NODE2_MOSI,
			output logic        NODE2_RESB,
			output logic        NODE2_DCR1B, //TDI
			output logic        NODE2_DCR2B, //TCK
			input  logic        NODE2_INTB,  // TDO
			output logic        NODE2_RFC,   //TMS
			output logic        NODE2_TESTMODE,
			output logic        NODE2_DSI_OFF,
			output logic [4:0]  NODE2_DBG,

			// ==== DSI Node 3 ====
			output logic        NODE3_CLKREF,
			input  logic        NODE3_CSB,
			input  logic        NODE3_SCK,
			input  logic        NODE3_MISO,
			input  logic        NODE3_MOSI,
			output logic        NODE3_RESB,
			output logic        NODE3_DCR1B, //TDI
			output logic        NODE3_DCR2B, //TCK
			input  logic        NODE3_INTB,  // TDO
			output logic        NODE3_RFC,   //TMS
			output logic        NODE3_TESTMODE,
			output logic        NODE3_DSI_OFF,
			output logic [4:0]  NODE3_DBG,

			// ==== DSI Node 4 ====
			output logic        NODE4_CLKREF,
			input  logic        NODE4_CSB,
			input  logic        NODE4_SCK,
			input  logic        NODE4_MISO,
			input  logic        NODE4_MOSI,
			output logic        NODE4_RESB,
			output logic        NODE4_DCR1B, //TDI
			output logic        NODE4_DCR2B, //TCK
			input  logic        NODE4_INTB,  // TDO
			output logic        NODE4_RFC,   //TMS
			output logic        NODE4_TESTMODE,
			output logic        NODE4_DSI_OFF,
			output logic [4:0]  NODE4_DBG,

			// ==== DSI Node 5 ====
			output logic        NODE5_CLKREF,
			input  logic        NODE5_CSB,
			input  logic        NODE5_SCK,
			input  logic        NODE5_MISO,
			input  logic        NODE5_MOSI,
			output logic        NODE5_RESB,
			output logic        NODE5_DCR1B, //TDI
			output logic        NODE5_DCR2B, //TCK
			input  logic        NODE5_INTB,  // TDO
			output logic        NODE5_RFC,   //TMS
			output logic        NODE5_TESTMODE,
			output logic        NODE5_DSI_OFF,
			output logic [4:0]  NODE5_DBG,

			// ==== DSI Node 6 ====
			output logic        NODE6_CLKREF,
			input  logic        NODE6_CSB,
			input  logic        NODE6_SCK,
			input  logic        NODE6_MISO,
			input  logic        NODE6_MOSI,
			output logic        NODE6_RESB,
			output logic        NODE6_DCR1B, //TDI
			output logic        NODE6_DCR2B, //TCK
			input  logic        NODE6_INTB,  // TDO
			output logic        NODE6_RFC,   //TMS
			output logic        NODE6_TESTMODE,
			output logic        NODE6_DSI_OFF,
			output logic [4:0]  NODE6_DBG,

			// ==== NODE Supply ====
			output logic        NODE_SUPPLY_OFF_FPGA,

			// ==== PICOSCOPE ====
			output logic [15:0] PICO,


			// ==== TP ====
			output logic        TP10,
			output logic        TP9,
			output logic        TP8,

			// ==== UMB ====
			input  logic        UMB_SCSN,
			output logic        UMB_MISO,
			input  logic        UMB_MOSI,
			input  logic        UMB_SCK,

			// ==== USB2SPI ====
			input  logic [3:0]  USB2SPI_GPIO   ,
			output logic        USB2SPI_MISO   ,
			input  logic        USB2SPI_MOSI   ,
			input  logic        USB2SPI_RESET  ,
			input  logic        USB2SPI_SCK    ,
			input  logic        USB2SPI_SS0O
		);

		`include "macro_defines_inc.sv"

	//==========================================================================
	// Input signals that will be muxed between MBIS and UMB
	//==========================================================================

	(* dont_touch = "yes" *) wire dbg_5_in, dbg_7_in;
	(* dont_touch = "yes" *) logic resb_in, clkref_ext; 

	ipad ipad_DBG_5_inst (.PAD(DBG_5), .C(dbg_5_in)); // internal PULL-UP enabled
	ipad ipad_DBG_7_inst (.PAD(DBG_7), .C(dbg_7_in)); // internal PULL-UP enabled

	always_comb begin
		case (SW[2])
			1'b0: begin // MBIS 
				resb_in    = dbg_5_in;
				clkref_ext = dbg_7_in;
			end
			1'b1: begin // UMB3
				resb_in    = dbg_7_in;
				clkref_ext = dbg_5_in;
			end
		endcase
	end
	
	//==========================================================================
	// CLOCKS
	//==========================================================================

	(* dont_touch = "yes" *) wire clk_100_c;

	ipad ipad_CLK_100_inst(.PAD(CLK_100), .C(clk_100_c)); // syn responsible for BUFG instance

	wire clk_sys_osc_pre;
	wire clk_10MHz;

	clk_wiz_multiple_clk clk_wiz_multiple_clk_inst(
			// Clock in ports
			.clk_in1(clk_100_c),

			// Clock out ports
			.clk_out1(clk_sys_osc_pre),
			.clk_out2(clk_10MHz),
			.clk_out3(),
			.clk_out4()
		);

	(* dont_touch = "yes" *) wire clk_18MHz;         // for internal use.

	BUFGCE bufg_clk_sys_osc(.I(clk_sys_osc_pre), .CE(1'b1), .O(clk_18MHz)) /* synthesis syn_noprune=1 */ /*synthesis syn_preserve=1 */ ;

	//==========================================================================
	// NRST/POR
	//==========================================================================

	(* dont_touch = "yes" *) wire dut_nreset_button, dut_nreset_in_umb, dut_nreset; // Taster DUT_RESET auf DSI3 12 Channel FPGA Master PCB

	ipad ipad_RESET_IN_inst (.PAD(DUT_RESET), .C(dut_nreset_button));
	ipad ipad_DEBUG_IN_15_inst  (.PAD(DBG_15), .C(dut_nreset_in_umb));
	
	assign dut_nreset = dut_nreset_button & dut_nreset_in_umb;
	// ==== POR ====
	
	wire npor_int;
	wire sync_nrst;
	
	por por_inst(.clk(clk_18MHz), .npor(npor_int));

	// synchronous power on reset
	utils_reset_sync utils_reset_nrst_osc_inst(
			.clk         (clk_18MHz),
			.i_nrst      (npor_int & dut_nreset),
			.o_nrst      (sync_nrst),
			.i_scan_mode (1'b0)
		);

	//==========================================================================
	// STARTUP DELAY
	//==========================================================================
	logic [23:0] r_startup_counter;
	logic        nrst_core;
	logic        init_if;

	always @(negedge sync_nrst or posedge clk_18MHz)
	begin
		if (!sync_nrst) begin
			r_startup_counter <= 24'hffffff; // ~419ms
			nrst_core <= 1'b0;
			init_if   <= 1'b0;
		end
		else begin
			init_if   <= 1'b0;
			if (|r_startup_counter) r_startup_counter <= r_startup_counter - 24'b1;
			if (r_startup_counter==24'h01ffff) init_if   <= 1'b1;
			if (r_startup_counter==24'h000000) nrst_core <= 1'b1;
		end
	end


	//==========================================================================
	// TST-MODE enable
	//==========================================================================

	//logic test_nrst;

	//ipad ipad_tmen_inst(.PAD(MAZ_JTAG_NTRST), .C(test_nrst));

	//==========================================================================
	// SYS_LED
	//==========================================================================

	wire [1:0] leds_sys_osc;

	opad opad_SYS_LED0_inst(.PAD(SYS_LED[0]), .I(leds_sys_osc[0]));
	opad opad_SYS_LED1_inst(.PAD(SYS_LED[1]), .I(leds_sys_osc[1]));

	//==========================================================================
	// BLINKER
	//==========================================================================

	blinker  #(
			.WITH_NRES_SYNC(0),
			.WITH_OBUF(0)
		) blinker_sys_osc_inst(
			.clk  (clk_18MHz),
			.nrst (sync_nrst),
			.leds (leds_sys_osc)
		);

	//==========================================================================
	// Tick generation for internal TCK
	//==========================================================================

	clk_reset_if dojtag_clk_rst();

	assign dojtag_clk_rst.clk = clk_18MHz;
	assign dojtag_clk_rst.rstn = sync_nrst;

	logic tick;

	tick_gen #(.ratio(8))
		tick_gen_tck_inst (
			.clk_rst (dojtag_clk_rst),
			.reset_sync(nrst_core),
			.tick_out(tick)
		);

	//==========================================================================
	// JTAG Master
	//==========================================================================

	logic jtag_master_tms;
	logic jtag_master_tdi;
	logic jtag_master_tck;
	logic jtag_master_trstn;
	logic jtag_master_finished;

	dojtag dojtag_inst(
			.rstn(sync_nrst),// low active reset
			.clk(clk_18MHz), //  clock
			.tick(tick),
			.soc(init_if & jtag_master_finished),
			.eoc(jtag_master_finished), // request was done, use handshake with soc
			.tms(jtag_master_tms),
			.tck(jtag_master_tck),
			.tdi(jtag_master_tdi),
			.trstn(jtag_master_trstn)
		);

	//==========================================================================
	// Supply switches
	//============================================set_msg_config==============================

	opad opad_NODE_SUPPLY_OFF_FPGA_inst        (.PAD(NODE_SUPPLY_OFF_FPGA       ),  .I(1'b0));
	opad opad_DSI_SUPPLY_OFF_1_TO_6_FPGA_inst  (.PAD(DSI_SUPPLY_OFF_1_TO_6_FPGA ),  .I(1'b0));
	opad opad_DSI_SUPPLY_OFF_7_TO_12_FPGA_inst (.PAD(DSI_SUPPLY_OFF_7_TO_12_FPGA),  .I(1'b0));

	//==========================================================================
	// CLK_REF generation / muxing
	//==========================================================================
	logic I_CLKREF, clkref_generated;
	
	
	/* Generation of internal 500 kHz clkref
	 * signal clkref_generated is always connected to 521.42 Nodes 
	 * to always have valid clkref at these nodes.
	 * Is connected to 521.43 Design via Multiplexor.
	 * */
	
	ClkDivider CLKREF_ClkDivider_inst (
			.clk (clk_10MHz),
			.clk_div(clkref_generated)
		);
	
	/* Multiplexing internal signal I_CLKREF
	 * Select: Dip-Switch SW[3]
	 * 	0 -> internal divided clkref_generated
	 * 	1 -> external signal connected to DBG_7
	 * using pure_mux here because SDC constraint using it*/
	(* dont_touch = "yes" *) pure_mux pure_mux_clkref_inst (
		.i_a(clkref_ext),
		.i_b(clkref_generated),
		.i_sa(SW[3]),
		.o_y(I_CLKREF));
	

	//==========================================================================
	// Connection to 52142 Nodes
	//==========================================================================
	dsi3_io_if dsi3_io[DSI3_COUNT-1:0] ();

	(* dont_touch = "yes" *) logic [DSI3_COUNT-1:0]  dsi_tx_muxed;
	//	(* dont_touch = "yes" *) logic [DSI3_TX_DAC_WIDTH-1:0] dsi3_txd_shaped[DSI_CHANNELS-1:0];

	logic [DSI3_COUNT-1:0]	I_DSI_RXD1;
	logic [DSI3_COUNT-1:0]	I_DSI_RXD2;


	generate
		for (genvar i=0; i<DSI3_COUNT; i=i+2) begin : generate_dsi_tx_mux
			always_comb begin
				dsi_tx_muxed[i]   = jtag_master_finished ? (!BUTTON[i]   & dsi3_io[i].txd_shaped[4]) : jtag_master_tms;
				dsi_tx_muxed[i+1] = jtag_master_finished ? (!BUTTON[i+1] & dsi3_io[i+1].txd_shaped[4]) : jtag_master_tdi;
			end
		end
	endgenerate


	generate
		for (genvar i=0; i<DSI_CHANNELS; i++) begin : dsi3_io_assign
			always_comb begin
				dsi3_io[i].rx[0] = I_DSI_RXD1[i];
				dsi3_io[i].rx[1] = I_DSI_RXD2[i];
				dsi3_io[i].ov = 1'b0;
				dsi3_io[i].uv = 1'b0;
			end
		end
	endgenerate

	`connect_52142_node(1)

	/* Rest of signals independent of number of DSI channels */
	opad opad_CLKREF_NODE1_inst (.PAD(NODE1_CLKREF), .I(clkref_generated));
	opad opad_CLKREF_NODE2_inst (.PAD(NODE2_CLKREF), .I(clkref_generated));
	opad opad_CLKREF_NODE3_inst (.PAD(NODE3_CLKREF), .I(clkref_generated));
	opad opad_CLKREF_NODE4_inst (.PAD(NODE4_CLKREF), .I(clkref_generated));
	opad opad_CLKREF_NODE5_inst (.PAD(NODE5_CLKREF), .I(clkref_generated));
	opad opad_CLKREF_NODE6_inst (.PAD(NODE6_CLKREF), .I(clkref_generated));

	opad opad_RESB_NODE1_inst (.PAD(NODE1_RESB), .I(sync_nrst));
	opad opad_RESB_NODE2_inst (.PAD(NODE2_RESB), .I(sync_nrst));
	opad opad_RESB_NODE3_inst (.PAD(NODE3_RESB), .I(sync_nrst));
	opad opad_RESB_NODE4_inst (.PAD(NODE4_RESB), .I(sync_nrst));
	opad opad_RESB_NODE5_inst (.PAD(NODE5_RESB), .I(sync_nrst));
	opad opad_RESB_NODE6_inst (.PAD(NODE6_RESB), .I(sync_nrst));

	//==========================================================================
	// logic_top instance
	//==========================================================================

	/*###   Interfaces / Signals   ######################################################*/
	clk_reset_if    clk_rst_top ();

	otp_io_if      otp_io ();
	tmr_scan_if    tmr_scan ();

	timebase_io_if timebase_io ();
	assign	timebase_io.clkref = I_CLKREF;
	assign	timebase_io.clkpll = clk_18MHz;
	assign	timebase_io.clkpll_div = I_CLKREF;

	supply_io_if supply_io ();
	assign	supply_io.ldo_ok = 1'b1;
	assign	supply_io.vcc_ok = 1'b1;
    assign  supply_io.vrr_ok = 1'b1;
	assign	supply_io.temp_warn = 1'b0;
	assign	supply_io.temp_error = 1'b0;

	/* Mux external SPI's to internal SPI*/
	spi_int_if spi_int ();
	always_comb begin
		case (SW[2:1])
			2'b00:	begin // USB2SPI Dongles
				spi_int.csb 	 = USB2SPI_SS0O;
				spi_int.csb_resn = ~USB2SPI_SS0O;
				spi_int.sdi 	 = USB2SPI_MOSI;
				spi_int.sck	 	 = USB2SPI_SCK & ~USB2SPI_SS0O;
			end
			2'b01: begin // MBIS Board
				spi_int.csb 	 = DBG_4;
				spi_int.csb_resn = ~DBG_4;
				spi_int.sdi 	 = DBG_2;
				spi_int.sck	 	 = DBG_3 & ~DBG_4;
			end
			2'b10,
			2'b11: begin // UMB
				spi_int.csb 	 = UMB_SCSN;
				spi_int.csb_resn = ~UMB_SCSN;
				spi_int.sdi 	 = UMB_MOSI; 
 				spi_int.sck	 	 = UMB_SCK & ~UMB_SCSN;
				end
			default: begin 
				spi_int.csb 	 = UMB_SCSN;
				spi_int.csb_resn = ~UMB_SCSN;
				spi_int.sdi 	 = UMB_MOSI; 
				spi_int.sck	 	 = UMB_SCK & ~UMB_SCSN;
				end
		endcase
	end
	
	pad_int_if syncb_pad();   //TCK
	pad_int_if rfc_pad();     //TDO
	pad_int_if intb_pad();
	pad_int_if dab_pad();    //TMS
	pad_int_if bfwb_pad();   //TCK

	opad opad_USB2SPI_MISO_inst (.PAD(USB2SPI_MISO), .I(spi_int.sdo));
	opad opad_UMB_MISO_inst     (.PAD(UMB_MISO),     .I(spi_int.sdo));
	//==========================================================================
	// DBG[0..7] DBG[8..15]
	//==========================================================================
	logic			tmode;

	opad opad_DEBUG_OUT_0_inst  (.PAD(DBG_0),  .I(1'b0));
	opad opad_DEBUG_OUT_1_inst  (.PAD(DBG_1),  .I(spi_int.sdo));
	//	opad opad_DEBUG_OUT_2_inst  (.PAD(DBG[2]),  .I(1'b0));
	//	opad opad_DEBUG_OUT_3_inst  (.PAD(DBG[3]),  .I(1'b0));
	//	opad opad_DEBUG_OUT_4_inst  (.PAD(DBG[4]),  .I(1'b0));
	//	opad opad_DEBUG_OUT_5_inst  (.PAD(DBG_5),  .I(1'b0));
	ipad ipad_DEBUG_OUT_6_inst  (.PAD(DBG_6), .C(tmode));
	//	opad opad_DEBUG_OUT_7_inst  (.PAD(DBG_7),  .I(1'b0));
	opad opad_DEBUG_OUT_8_inst  (.PAD(DBG_8),  .I(1'b0));
	opad opad_DEBUG_OUT_9_inst  (.PAD(DBG_9),  .I(intb_pad.out));
	opad opad_DEBUG_OUT_10_inst (.PAD(DBG_10), .I(dab_pad.out));
	opad opad_DEBUG_OUT_11_inst (.PAD(DBG_11), .I(bfwb_pad.out));
	// JIRA-
	//  ipad ipad_DEBUG_OUT_12_inst (.PAD(DBG_12), .C(syncb_pad.in_a));
	iopad iopad_DEBUG_INOUT_12_inst (
		.I  (syncb_pad.out),
		.IE (syncb_pad.ie ),
		.OEN(~syncb_pad.oe),
		.C  (syncb_pad.in_a  ),
		.PAD(DBG_12)
	);
	opad opad_DEBUG_OUT_13_inst (.PAD(DBG_13), .I(rfc_pad.out));
	opad opad_DEBUG_OUT_14_inst (.PAD(DBG_14), .I(1'b0));
	//opad opad_DEBUG_OUT_15_inst (.PAD(DBG_15), .I(1'b0));


	always_comb begin
		rfc_pad.in_a  = 1'b0;
		intb_pad.in_a = 1'b0;
		dab_pad.in_a  = 1'b0;
		bfwb_pad.in_a = 1'b0;
	end

	logic I_CLKOSC, I_RESB, I_PORB;
	always_comb begin
		I_CLKOSC = clk_18MHz;
		I_RESB = dut_nreset & resb_in;
		I_PORB = nrst_core;
	end


	//==========================================================================
	// JTAG muxing
	//==========================================================================

	jtag_pad_if		jtag();
	
	always_comb begin
		jtag.tdi	= tmode && MAZ_JTAG_TDI_TDA;
		jtag.tck	= tmode && MAZ_JTAG_TCK;
		jtag.tms	= tmode && MAZ_JTAG_TMS;
		jtag.trstn	= tmode;
		jtag.tmode	= tmode;
		MAZ_JTAG_TDO	= jtag.tdo;
	end

	/* TMR's */
	tmr_dsi_if        tmr_dsi[DSI_CHANNELS-1:0]();
	tmr_osc_if        tmr_osc();
	tmr_supply_if     tmr_supply();
	tmr_out_osc_if    tmr_out_osc ();
	tmr_out_supply_if tmr_out_supply ();
	tmr_out_dsi_if    tmr_out_dsi[DSI_CHANNELS-1:0] ();
	tmr_top_if        tmr_top();


	always_comb begin
		tmr_osc.tmr_ana_tb_osc = 3'b0;
		tmr_osc.tmr_ana_tb_pll = 7'b0;

		tmr_supply.tmr_ana_supply = 6'b0;
		tmr_supply.tmr_ana_temp_sensor = 2'b0;
		tmr_supply.tmr_ana_otp = 6'b0;
	end

	generate
		for (genvar i=0; i<DSI_CHANNELS; i++) begin : tmr_dsi_assign
			always_comb begin
				tmr_dsi[i].tmr_ana_dsi3_rx = 2'b00;
				tmr_dsi[i].tmr_ana_dsi3_tx = 7'b0;
				tmr_dsi[i].tmr_in = 4'b0000;
			end
		end
	endgenerate
	
	
	/* mapping for logic_top instance */
	logic i_clock_osc;
	logic i_resb;
	logic i_por_n;
	assign i_clock_osc = I_CLKOSC;
	assign i_resb = I_RESB;
	assign i_por_n = I_PORB;
	
	(* dont_touch = "yes" *) logic_top i_logic_top (
   	.i_clock_osc   (i_clock_osc   ),
   	.i_resb        (i_resb        ),
   	.i_por_n       (i_por_n       ),
   	.clk_rst_top   (clk_rst_top   ),
   	.spi_int       (spi_int       ),
   	.jtag          (jtag          ),
   	.dsi3_io       (dsi3_io       ),
   	.timebase_io   (timebase_io   ),
   	.supply_io     (supply_io     ),
   	.otp_io        (otp_io        ),
   	.tmr_dsi       (tmr_dsi       ),
   	.tmr_out_dsi   (tmr_out_dsi   ),
   	.tmr_osc       (tmr_osc       ),
   	.tmr_out_osc   (tmr_out_osc   ),
   	.tmr_supply    (tmr_supply    ),
   	.tmr_out_supply(tmr_out_supply),
   	.tmr_scan      (tmr_scan      ),
   	.tmr_top       (tmr_top       ),
   	.dab_pad       (dab_pad       ),
   	.bfwb_pad      (bfwb_pad      ),
   	.rfc_pad       (rfc_pad       ),
   	.intb_pad      (intb_pad      ),
   	.syncb_pad     (syncb_pad     ),
   	.o_otp_ehv     (o_otp_ehv     )
   );

	//==========================================================================
	// picoscobe digital interface
	//==========================================================================
	logic rxd_ored;

	always_comb begin
		rxd_ored = ( |I_DSI_RXD1 ) | ( |I_DSI_RXD2 );
	end

	opad opad_pico_0_inst  (.PAD(PICO[0]),  .I(I_DSI_RXD1[0] ));
	opad opad_pico_1_inst  (.PAD(PICO[1]),  .I(I_DSI_RXD2[0] ));
	opad opad_pico_2_inst  (.PAD(PICO[2]),  .I(I_DSI_RXD1[1] ));
	opad opad_pico_3_inst  (.PAD(PICO[3]),  .I(I_DSI_RXD2[1] ));
	opad opad_pico_4_inst  (.PAD(PICO[4]),  .I(intb_pad.out));
	opad opad_pico_5_inst  (.PAD(PICO[5]),  .I(dab_pad.out)); 
	opad opad_pico_6_inst  (.PAD(PICO[6]),  .I(bfwb_pad.out));
	opad opad_pico_7_inst  (.PAD(PICO[7]),  .I(rfc_pad.out));
	opad opad_pico_8_inst  (.PAD(PICO[8]),  .I(I_CLKREF));
	opad opad_pico_9_inst  (.PAD(PICO[9]),  .I(I_RESB));
	opad opad_pico_10_inst (.PAD(PICO[10]), .I(syncb_pad.in_a));
	opad opad_pico_11_inst (.PAD(PICO[11]), .I(rxd_ored	    ));
	opad opad_pico_12_inst (.PAD(PICO[12]), .I(spi_int.csb ));
	opad opad_pico_13_inst (.PAD(PICO[13]), .I(spi_int.sck  ));
	opad opad_pico_14_inst (.PAD(PICO[14]), .I(spi_int.sdi ));
	opad opad_pico_15_inst (.PAD(PICO[15]), .I(spi_int.sdo ));

endmodule

