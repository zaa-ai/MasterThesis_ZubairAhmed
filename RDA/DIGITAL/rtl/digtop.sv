`define IO_PAD_CONNECTION( _name )  input  logic I_``_name , \
output logic O_``_name , \
output logic O_``_name``_OE , \
output logic O_``_name``_IE , \
output logic O_``_name``_PD , \
output logic O_``_name``_PU ,

/**
 * Module: digtop
 *
 * Digital part top module
 */
module digtop import project_pkg::*; #(
		parameter	DSI3_TX_DAC_WIDTH       = 5,
		parameter	DSI3_TX_TBIT_CFG_WIDTH  = 2,
		parameter	DSI3_RX_TRIM_WIDTH      = 4,
        parameter   DSI3_IDAC_WIDTH         = 5,
		parameter	TRIM_IREF_WIDTH			= 4,
		parameter	TRIM_OSC_F_WIDTH		= 7,
		parameter	TRIM_OSC_TCF_WIDTH		= 3,
		parameter 	DSI3_COUNT              = DSI_CHANNELS,
		parameter	DSI3_ATST_TX_WIDTH      = 7,
		parameter	DSI3_ATST_RX_WIDTH      = 1,
		parameter	VDSI_CTRL_WIDTH         = 3
	)(
		//SPI
		`IO_PAD_CONNECTION(CSB)
		`IO_PAD_CONNECTION(SCK)
		`IO_PAD_CONNECTION(SDI)
		`IO_PAD_CONNECTION(SDO)
		`IO_PAD_CONNECTION(RFC)
		`IO_PAD_CONNECTION(INTB)
		`IO_PAD_CONNECTION(DAB)
		`IO_PAD_CONNECTION(BFWB)
		`IO_PAD_CONNECTION(SYNCB)

		// general
		input	logic		I_PORB,
		input	logic		I_CLKREF,
		input	logic		I_RESB,
		output  logic       O_CLKREF_IE,
		output	logic		O_PAD_DS,
		output	logic[TRIM_IREF_WIDTH-1:0]	O_TRIM_I5U,
		output	logic		O_VDD_VOLTAGE_DIVIDER_DISABLE,
		output  logic       O_VDD_LOAD_DISABLE,
		output  logic       O_VDD_DISABLE,
		output	logic		O_CLKREF_DIV,
		
		// PLL/OSC
		input	logic		I_CLKOSC,
		input	logic		I_CLKPLL,
		input   logic		I_CLKPLL_DIV,
		input	logic		I_OSC_READY,
		input	logic		I_PLL_DOWN_MON,
		input	logic		I_PLL_UP_MON,
		input	logic		I_PLL_LOCK_MON,

		output  logic		O_OSC_ON,
		output  logic		O_PLL_HOLD,
		output  logic		O_PLL_ON,

		output  logic[TRIM_OSC_F_WIDTH-1:0]	    O_TRIM_OSC_F,
		output  logic[TRIM_OSC_TCF_WIDTH-1:0]	O_TRIM_OSC_TCF,

		output  logic[2:0]	O_ATST_OSC,
		output  logic[6:0]	O_ATST_PLL,

		// power supply
		input	logic 		I_VCC_OK,
		input   logic       I_VRR_OK,
		input	logic		I_LDO_OK,
		output	logic		O_LDO_EN,

		// DSI - transmitter
		input	logic[DSI3_COUNT-1:0]	I_DSI_UVB,
		input	logic[DSI3_COUNT-1:0]	I_DSI_OV,
		output	logic[DSI3_COUNT-1:0]	O_DSI_TX_ON,
		output	logic[DSI3_COUNT-1:0]	O_DSI_TX_HVCASC_ON,
		output	logic[DSI3_COUNT*DSI3_TX_DAC_WIDTH-1:0]	O_DSI_TX_DATA,
		output  logic[DSI3_COUNT-1:0]	O_DSI_RX_TXN,
		output  logic[DSI3_COUNT*DSI3_TX_TBIT_CFG_WIDTH-1:0]   O_DSI_TX_TBIT_CFG,
        
        input   logic[DSI3_COUNT-1:0]   I_DSI_ICMP,
        output  logic[DSI3_COUNT*DSI3_IDAC_WIDTH-1:0] O_DSI_IDAC,

		// DSI - receiver
		input	logic[DSI3_COUNT-1:0]	I_DSI_RXD1,
		input	logic[DSI3_COUNT-1:0]	I_DSI_RXD2,
		output	logic[DSI3_COUNT-1:0]	O_DSI_RX_ON,
		output  logic[DSI3_COUNT-1:0]	O_DSI_RX_FILTER_FAST,
		output	logic[DSI3_COUNT*DSI3_RX_TRIM_WIDTH-1:0]	O_TRIM_DSI_RX1,
		output	logic[DSI3_COUNT*DSI3_RX_TRIM_WIDTH-1:0]	O_TRIM_DSI_RX2,

		// OT
		input	logic		I_OT_ERROR,
		input	logic		I_OT_WARN,
		output	logic[1:0]	O_ATST_TEMP_SENSOR,
		output	logic[1:0]	O_TRIM_OT,

		// amux
		output	logic[4:0]	O_ATST_SUP,
		output	logic[DSI3_COUNT*DSI3_ATST_TX_WIDTH-1:0]	O_ATST_TX,
		output	logic[DSI3_COUNT*DSI3_ATST_RX_WIDTH-1:0]	O_ATST_RX,
		output	logic					O_AOUT_ENABLE,

		// test
		// @SuppressProblem -nowarnmiss 1 -type mix_reset_non_reset_signal -count 1 -length 1
		input logic 		I_TMODE,
`ifdef VCS
		// @SuppressProblem -nowarnmiss 1 -type fully_unread_net -count 5 -length 3
		input				VDD, VSS,
		input               PSUB, VDD_NBL,
		input logic         VCC,
`endif
		// OTP
		output  logic[5:0]	O_ATST_OTP,
		input logic         A_OTP_EHV,
//		output logic 		A_OTP_VBG,
		output logic 		A_OTP_VPP,
		output logic 		A_OTP_VREF,
		output logic 		A_OTP_VRR,
		output logic		O_OTP_EHV
	);
    
	import project_pkg::*;

	/*###   Interfaces / Signals   ######################################################*/
	clk_reset_if	clk_rst ();
	
	spi_int_if 		spi_int ();
	dsi3_io_if 		dsi3_io[DSI_CHANNELS-1:0]();
	timebase_io_if	timebase_io ();
	supply_io_if	supply_io ();
	otp_io_if		otp_io ();
	jtag_pad_if		jtag();
	
	tmr_dsi_if		tmr_dsi[DSI_CHANNELS-1:0]();
	tmr_osc_if  	tmr_osc();
	tmr_supply_if	tmr_supply();
	tmr_scan_if		tmr_scan ();
	tmr_top_if		tmr_top();
	
	tmr_out_supply_if tmr_out_supply ();
	tmr_out_osc_if tmr_out_osc ();
	tmr_out_dsi_if tmr_out_dsi[DSI_CHANNELS-1:0] ();
	
	`define pad_interface_definition(_pad_)	pad_int_if  	_pad_``_pad(), _pad_``_pad_out();
	
	`pad_interface_definition(csb)
	`pad_interface_definition(sck)
	`pad_interface_definition(mosi)
	`pad_interface_definition(miso)
	
	`pad_interface_definition(rfc)
	`pad_interface_definition(intb)
	`pad_interface_definition(dab)
	`pad_interface_definition(bfwb)
	`pad_interface_definition(syncb)
	
	logic	clk_osc;
	
	// @SuppressProblem -nowarnmiss 1 -type   fully_unread_variable -count 1 -length 1
	logic	atpgmode, scan_enable;  
	
	assign	atpgmode = tmr_scan.scan;
	assign	O_PAD_DS = (atpgmode == 1'b1) ? 1'b1 : supply_io.pad_drive_strength;
	assign	O_CLKREF_IE = 1'b1;
	
`ifdef target_technology_FPGA
    assign scan_enable = 1'b0;
`else
    pure_and pure_and_scan_enable (
            .i_a   (I_RFC),
            .i_b   (atpgmode),
            .o_y   (scan_enable));
`endif    
	tmr_out_test_vector_t	tmr_out_signals;
	logic	bfwb_muxed;
	
	/*###   general   ######################################################*/
	assign	O_VDD_VOLTAGE_DIVIDER_DISABLE = tmr_scan.vdd_voltage_divider_disable;
	assign	O_VDD_DISABLE = tmr_scan.vdd_disable;
	assign	O_AOUT_ENABLE	= (atpgmode == 1'b1) ? '0 : tmr_top.tmr_ana;
	assign  O_VDD_LOAD_DISABLE = tmr_scan.vdd_load_disable;
	
	assign	tmr_scan.scan_clock = I_BFWB;
	assign	tmr_scan.scan_reset = I_RESB;
	
	/*###   DSI3   ######################################################*/
	generate
		for (genvar i=0; i<DSI_CHANNELS; i++) begin : generate_vector_trim_rx
			//TODO: scan mux me?!
			assign	O_TRIM_DSI_RX1[(DSI3_RX_TRIM_WIDTH*(i+1))-1-:DSI3_RX_TRIM_WIDTH] = dsi3_io[i].trim_rx1;
			assign	O_TRIM_DSI_RX2[(DSI3_RX_TRIM_WIDTH*(i+1))-1-:DSI3_RX_TRIM_WIDTH] = dsi3_io[i].trim_rx2;  //TODO: scan loop?
			assign	O_DSI_TX_DATA [(DSI3_TX_DAC_WIDTH *(i+1))-1-:DSI3_TX_DAC_WIDTH ] = dsi3_io[i].txd_shaped; //TODO: scan loop?
			assign	O_DSI_TX_ON[i] = (atpgmode == 1'b0) ? dsi3_io[i].tx_on :  '0 ;
			assign	O_DSI_TX_HVCASC_ON[i] = (atpgmode == 1'b1) ? '0 : dsi3_io[i].tx_hvcasc_on;
			assign	O_DSI_RX_TXN[i] = dsi3_io[i].receive_mode_enable;
			assign	O_DSI_RX_ON[i] = (atpgmode == 1'b1) ? '0 : dsi3_io[i].rx_on;
			assign	O_DSI_RX_FILTER_FAST[i] = dsi3_io[i].short_filter_time;
			assign	O_DSI_TX_TBIT_CFG[(DSI3_TX_TBIT_CFG_WIDTH*(i+1))-1-:DSI3_TX_TBIT_CFG_WIDTH]	= dsi3_io[i].bit_time;
			assign	O_DSI_IDAC[(DSI3_IDAC_WIDTH*(i+1))-1-:DSI3_IDAC_WIDTH]	= dsi3_io[i].rx_idac;
			
			assign	dsi3_io[i].rx[0] = (atpgmode == 1'b0) ? I_DSI_RXD1[i] : dsi3_io[i].tx_on;
			assign	dsi3_io[i].rx[1] = (atpgmode == 1'b0) ? I_DSI_RXD2[i] : dsi3_io[i].tx_hvcasc_on;
			assign	dsi3_io[i].ov    = (atpgmode == 1'b0) ? I_DSI_OV[i]   : dsi3_io[i].receive_mode_enable;
			assign	dsi3_io[i].uv    = (atpgmode == 1'b0) ? ~I_DSI_UVB[i] : dsi3_io[i].rx_on ^ dsi3_io[i].short_filter_time;
			assign	dsi3_io[i].i_q   = (atpgmode == 1'b0) ? I_DSI_ICMP[i] : supply_io.trim_ot[i];
			
			assign	O_ATST_TX[(DSI3_ATST_TX_WIDTH*(i+1))-1-:DSI3_ATST_TX_WIDTH]	= (atpgmode == 1'b0) ? tmr_dsi[i].tmr_ana_dsi3_tx : '0;
			assign	O_ATST_RX[(DSI3_ATST_RX_WIDTH*(i+1))-1-:DSI3_ATST_RX_WIDTH]	= (atpgmode == 1'b0) ? tmr_dsi[i].tmr_ana_dsi3_rx : '0;
		end
	endgenerate

	/*###   osc/PLL   ######################################################*/
	assign	O_CLKREF_DIV = timebase_io.clkref_div;
	assign	O_PLL_HOLD = (atpgmode == 1'b1) ? '0 : timebase_io.pll_hold;
	assign	O_PLL_ON = (atpgmode == 1'b1) ? '0 : timebase_io.pll_on;
	assign	O_TRIM_OSC_F = timebase_io.trim_osc_f;
	assign	O_TRIM_OSC_TCF = timebase_io.trim_osc_tcf;
	assign	timebase_io.clkpll			= (atpgmode == 1'b0) ? I_CLKPLL			: tmr_scan.scan_clock;
	assign	timebase_io.clkref			= (atpgmode == 1'b0) ? I_CLKREF			: ^(timebase_io.trim_osc_f[2:0]);
	assign	timebase_io.clkpll_div		= (atpgmode == 1'b0) ? I_CLKPLL_DIV		: ^(timebase_io.trim_osc_f[TRIM_OSC_F_WIDTH-1:3]);
	assign	timebase_io.pll_down_mon	= (atpgmode == 1'b0) ? I_PLL_DOWN_MON	: timebase_io.trim_osc_tcf[0];
	assign	timebase_io.pll_up_mon		= (atpgmode == 1'b0) ? I_PLL_UP_MON		: timebase_io.trim_osc_tcf[1];
	assign	timebase_io.pll_lock_mon	= (atpgmode == 1'b0) ? I_PLL_LOCK_MON	: timebase_io.trim_osc_tcf[2];
	
	assign	O_ATST_OSC = (atpgmode == 1'b1) ? '0 : tmr_osc.tmr_ana_tb_osc;
	assign	O_ATST_PLL = (atpgmode == 1'b1) ? '0 : tmr_osc.tmr_ana_tb_pll;
	
	assign	O_OSC_ON = I_PORB & ~tmr_scan.disable_osc;

	/*###   supply   ######################################################*/
	assign	supply_io.ldo_ok	= (atpgmode == 1'b0) ? I_LDO_OK		: supply_io.ldo_en;
	assign	supply_io.temp_error= (atpgmode == 1'b0) ? I_OT_ERROR	: ^(O_DSI_IDAC[9:8]);
	assign	supply_io.temp_warn	= (atpgmode == 1'b0) ? I_OT_WARN	: timebase_io.pll_hold;
	assign	supply_io.vcc_ok	= (atpgmode == 1'b0) ? I_VCC_OK		: timebase_io.pll_on;
	assign	supply_io.vrr_ok	= (atpgmode == 1'b0) ? I_VRR_OK		: tmr_top.tmr_ana;
	assign	O_TRIM_I5U			= supply_io.trim_iref;
	assign	O_LDO_EN			= (atpgmode == 1'b0) ? supply_io.ldo_en : '0;
	assign	O_ATST_SUP			= (atpgmode == 1'b0) ? tmr_supply.tmr_ana_supply : '0; //TODO: check scan muxing necessary
	assign	O_ATST_TEMP_SENSOR	= (atpgmode == 1'b0) ? tmr_supply.tmr_ana_temp_sensor : '0; //TODO: check scan muxing necessary
	assign  O_TRIM_OT			= supply_io.trim_ot;

	/*###   pads   ######################################################*/
	logic	csb_test_ie, sck_test_ie, mosi_test_ie, miso_test_ie, rfc_test_ie, dab_test_ie, bfwb_test_ie, syncb_test_ie, intb_test_ie;
	logic	csb_test_out, sck_test_out, mosi_test_out, miso_test_out, rfc_test_out, dab_test_out, bfwb_test_out, syncb_test_out, intb_test_out;
	spi_interface_generator i_spi_interface_generator (
		.spi_int     (spi_int.master    ), 
		.csb         (csb_pad.master    ), 
		.sck         (sck_pad.master    ), 
		.sdi         (mosi_pad.master   ), 
		.sdo         (miso_pad.master   ),
		.i_scan_clock(I_SCK),
		.i_scan_reset(tmr_scan.scan_reset),
		.i_scanmode  (atpgmode          ),
		.i_sdi_scan_input(miso_pad.out    ),
		.i_csb_scan_input(bfwb_pad_out.ie ^ csb_pad_out.ie ^ dab_pad_out.ie ^ intb_pad_out.ie ^ miso_pad_out.ie ^
							mosi_pad_out.ie ^ rfc_pad_out.ie ^ sck_pad_out.ie ^ syncb_pad_out.ie) //TODO: Use a simpler value to set CSB in scan
	);
	
	//TODO: output mux needed for output signal

	`define pad_output_assignments(_pin_name_, _pad_, _scan_out_, _scan_oe_, _scan_ie_)  \
		O_``_pin_name_`` 	= (atpgmode == 1'b0) ? _pad_``_pad_out.out : _scan_out_ ; \
		O_``_pin_name_``_OE = (atpgmode == 1'b0) ? _pad_``_pad_out.oe  : _scan_oe_ ; \
		O_``_pin_name_``_IE = (atpgmode == 1'b0) ? _pad_``_pad_out.ie  : _scan_ie_ ; \
		O_``_pin_name_``_PD = (atpgmode == 1'b0) ? _pad_``_pad_out.pd  : 1'b0; \
		O_``_pin_name_``_PU = (atpgmode == 1'b0) ? _pad_``_pad_out.pu  : 1'b0;
		
	`define pad_assignments(_pin_name_, _pad_, _scan_in_, _scan_out_, _scan_oe_, _scan_ie_) always_comb begin \
		_pad_``_pad_out.in_a	= (atpgmode == 1'b0) ? I_``_pin_name_ 	  : _scan_in_ ; \
		`pad_output_assignments( _pin_name_, _pad_, _scan_out_, _scan_oe_, _scan_ie_) \
	end
	`define pad_assignments_wo_input(_pin_name_, _pad_, _scan_out_, _scan_oe_, _scan_ie_) always_comb begin \
		_pad_``_pad_out.in_a	= I_``_pin_name_; \
		`pad_output_assignments( _pin_name_, _pad_, _scan_out_, _scan_oe_, _scan_ie_) \
	end

    //                        pad    pad_if   out   oe    ie
	`pad_assignments_wo_input(CSB,   csb,   1'b0, 1'b0, 1'b1)	// scan data in 3 
    
    //               pad    pad_if  scan_in              out   oe    ie
    `pad_assignments(SCK,   sck,   I_SCK              , 1'b0, 1'b0, 1'b1) // 
	`pad_assignments(SDI,   mosi,  1'b0               , 1'b0, 1'b0, 1'b1) // scan data in 2
	`pad_assignments(SDO,   miso,  1'b0               , 1'b0, 1'b1, 1'b0) // scan data out 1
	
	`pad_assignments(RFC,   rfc,   ^(O_DSI_IDAC[1:0]) , 1'b0, 1'b0, 1'b1) // scan enable
	`pad_assignments(BFWB,  bfwb,  ^(O_DSI_RX_ON[1:0]), 1'b0, 1'b0, 1'b1) // scan clock 
	`pad_assignments(DAB,   dab,   ^(O_DSI_IDAC[3:2]) , 1'b0, 1'b0, 1'b1) // scan data in 1
	`pad_assignments(INTB,  intb,  ^(O_DSI_IDAC[5:4]) , 1'b0, 1'b1, 1'b0) // scan data out 2
	`pad_assignments(SYNCB, syncb, ^(O_DSI_IDAC[7:6]) , 1'b0, 1'b1, 1'b0) // scan data out 3
	
	`define pad_mux_test(_pad_) pad_mux_test i_pad_mux_test_``_pad_ ( \
		.clk_rst              (clk_rst.slave               ), \
		.pad_out              (_pad_``_pad_out.master      ), \
		.pad_appl             (_pad_``_pad.slave           ), \
		.i_enable_input       (_pad_``_test_ie             ), \
		.i_test_en            (tmr_top.tmr_out_en_``_pad_  ), \
		.i_test_sel           (tmr_top.tmr_out_sel_``_pad_ ), \
		.i_test_vector        (tmr_out_signals             ), \
		.o_test_out           (_pad_``_test_out            ));
		
	`define pad_mux_test_jtag_inputs(_pad_) pad_mux_test_jtag_inputs i_pad_mux_test_``_pad_ ( \
		.clk_rst              (clk_rst.slave               ), \
		.pad_out              (_pad_``_pad_out.master      ), \
		.pad_appl             (_pad_``_pad.slave           ), \
		.i_use_jtag_inputs    (tmr_top.tmr_dig_use_jtag    ), \
		.i_enable_input       (_pad_``_test_ie             ), \
		.i_test_en            (tmr_top.tmr_out_en_``_pad_  ), \
		.i_test_sel           (tmr_top.tmr_out_sel_``_pad_ ), \
		.i_test_vector        (tmr_out_signals             ), \
		.o_test_out           (_pad_``_test_out            ));
		
	`pad_mux_test(csb)
	`pad_mux_test(sck)
	`pad_mux_test(mosi)
	`pad_mux_test(miso)

	`pad_mux_test(rfc)
	`pad_mux_test(intb)
	`pad_mux_test_jtag_inputs(syncb)
	`pad_mux_test_jtag_inputs(bfwb)
	`pad_mux_test_jtag_inputs(dab)
	
	assign	jtag.tms = I_DAB & I_TMODE;
	assign	jtag.tdi = I_SYNCB & I_TMODE;
	assign	jtag.trstn = atpgmode ? tmr_scan.scan_reset : I_TMODE & I_PORB;
	assign	jtag.tmode = I_TMODE;
	
	pure_clk_gate_latch i_pure_clk_gate_latch_tck (
		.in_clk_e    (I_TMODE   ),
		.in_clk      (I_BFWB    ),
		.out_clk     (jtag.tck  ),
		.scan_mode   (atpgmode  ));
	
	logic	osc_ready_synced;
	clk_reset_if clk_rst_for_sync_osc_ready ();
	assign	clk_rst_for_sync_osc_ready.clk = (atpgmode == 1'b0) ? I_CLKOSC : tmr_scan.scan_clock;
	assign	clk_rst_for_sync_osc_ready.rstn = (tmr_scan.scan == 1'b0) ? I_PORB & ~tmr_scan.disable_osc : tmr_scan.scan_reset;
	
	logic	osc_ready_with_scan;
	assign	osc_ready_with_scan = (atpgmode == 1'b0) ? I_OSC_READY : supply_io.trim_iref[0];
	
`ifdef target_technology_FPGA
    assign osc_ready_synced = 1'b1;
	assign clk_osc = I_CLKOSC;
`else
	sync i_sync_osc_ready (
		.clk_rst     (clk_rst_for_sync_osc_ready.slave    ), 
		.i_in        (osc_ready_with_scan | tmr_top.tmr_dig_ignore_osc_ready), 
		.o_test_out  (			 ), 
		.o_out       (osc_ready_synced  ));
	
	pure_clk_gate_latch i_pure_clk_gate_latch_clk (
			.in_clk_e    (osc_ready_synced   ),
			.in_clk      (I_CLKOSC   ), 
			.out_clk     (clk_osc    ),
			.scan_mode   (atpgmode  ));
`endif	
	logic	clk_osc_scan_muxed;
	pure_mux i_pure_mux_clkosc_for_scan (
		.i_a         (tmr_scan.scan_clock ), 
		.i_b         (clk_osc            ), 
		.i_sa        (tmr_scan.scan       ), 
		.o_y         (clk_osc_scan_muxed  ));
	
	
	/*###   TMR_OUT   ######################################################*/
	assign	bfwb_muxed = (atpgmode == 1'b0) ? I_BFWB : supply_io.pad_drive_strength;
	assign	tmr_out_signals[2:0] = {jtag.tdo, 1'b1, 1'b0};
	always_comb begin
		if (atpgmode == 1'b0)
			tmr_out_signals[12:3] = {I_RESB, I_SYNCB, bfwb_muxed, I_DAB, I_INTB, I_RFC, I_SDI, I_SDO, I_SCK, I_CSB}; // TODO: add synced signals?
		else begin
			tmr_out_signals[12:3] = {^(O_TRIM_DSI_RX1), syncb_test_out, bfwb_test_out, dab_test_out, intb_test_out, rfc_test_out, mosi_test_out, miso_test_out, sck_test_out, csb_test_out};
		end
	end
	always_comb begin
		if (tmr_top.tmr_dig_sel_sync == 1'b1)
			tmr_out_signals[17:13] = tmr_out_supply.value;
		else
			tmr_out_signals[17:13] = tmr_out_supply.value_synced;
	end
	assign	tmr_out_signals[31:18] = tmr_out_osc.value;
	assign	tmr_out_signals[32]    = (atpgmode == 1'b0) ? I_OSC_READY : tmr_top.tmr_dig_ignore_osc_ready;
	generate
		genvar k;
		for (k=0; k<DSI_CHANNELS; k++) begin : generate_DSI3_tmr_out_assignments
			always_comb begin
				if (tmr_top.tmr_dig_sel_sync == 1'b1)
					tmr_out_signals[(33+5*(k+1)-1):(33+5*k)] = tmr_out_dsi[k].value;
				else
					tmr_out_signals[(33+5*(k+1)-1):(33+5*k)] = tmr_out_dsi[k].value_synced;
			end
		end
    endgenerate
    assign  tmr_out_signals[48:43] = '0;
	assign	tmr_out_signals[49] = osc_ready_synced;
	assign	tmr_out_signals[50] = otp_io.otp_ready;
	generate
		genvar m;
		for (m=0; m<DSI_CHANNELS; m++) begin : generate_DSI3_tmr_out_assignments_filtered
			always_comb begin
				tmr_out_signals[(51+2*(m+1)-1):(51+2*m)] = tmr_out_dsi[m].rx_filtered;
			end
		end
	endgenerate
    assign  tmr_out_signals[58:55] = '0;
	
	always_comb begin
		tmr_out_osc.clock_selected = 1'b0;
		if (((tmr_top.tmr_out_sel_bfwb	> 6'd17) && (tmr_top.tmr_out_sel_bfwb	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_csb 	> 6'd17) && (tmr_top.tmr_out_sel_csb 	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_dab	> 6'd17) && (tmr_top.tmr_out_sel_dab	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_intb	> 6'd17) && (tmr_top.tmr_out_sel_intb	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_miso	> 6'd17) && (tmr_top.tmr_out_sel_miso	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_mosi	> 6'd17) && (tmr_top.tmr_out_sel_mosi	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_rfc	> 6'd17) && (tmr_top.tmr_out_sel_rfc	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_sck	> 6'd17) && (tmr_top.tmr_out_sel_sck	< 6'd30)) ||   
			((tmr_top.tmr_out_sel_syncb	> 6'd17) && (tmr_top.tmr_out_sel_syncb	< 6'd30))    ) begin
			tmr_out_osc.clock_selected = 1'b1;
		end
	end
	
	/*###   TMR_IN   ######################################################*/
	logic[3:0]	tmr_in;
	logic[10:0]	gpio_inputs;
	assign	gpio_inputs = (atpgmode == 1'b0) ? {
			I_CLKREF,
			I_INTB,
			I_SYNCB,
			bfwb_muxed,
			I_DAB,
			I_RFC,
			I_SDO,
			I_SDI,
			I_SCK,
			I_CSB,
			1'b0
		} : {O_TRIM_DSI_RX2, O_DSI_TX_TBIT_CFG[3:2], ^(O_DSI_TX_TBIT_CFG[1:0])};
    
	always_comb begin
		csb_test_ie = 1'b0;
		sck_test_ie = 1'b0;
		mosi_test_ie = 1'b0;
		miso_test_ie = 1'b0;
		rfc_test_ie = 1'b0;
		dab_test_ie = 1'b0;
		bfwb_test_ie = 1'b0;
		syncb_test_ie = 1'b0;
		intb_test_ie = 1'b0;
		for (int i=0; i<4; i++) begin
			csb_test_ie  |= (tmr_top.tmr_in[i] == 4'd1) ? 1'b1 : 1'b0;
			sck_test_ie  |= (tmr_top.tmr_in[i] == 4'd2) ? 1'b1 : 1'b0;
			mosi_test_ie |= (tmr_top.tmr_in[i] == 4'd3) ? 1'b1 : 1'b0;
			miso_test_ie |= (tmr_top.tmr_in[i] == 4'd4) ? 1'b1 : 1'b0;
			rfc_test_ie  |= (tmr_top.tmr_in[i] == 4'd5) ? 1'b1 : 1'b0;
			dab_test_ie  |= (tmr_top.tmr_in[i] == 4'd6) ? 1'b1 : 1'b0;
			bfwb_test_ie |= (tmr_top.tmr_in[i] == 4'd7) ? 1'b1 : 1'b0;
			syncb_test_ie|= (tmr_top.tmr_in[i] == 4'd8) ? 1'b1 : 1'b0;
			intb_test_ie |= (tmr_top.tmr_in[i] == 4'd9) ? 1'b1 : 1'b0;
		end
		//syncb, bfwb, dab -> tmr_top.tmr_dig_use_jtag
	end
	generate
		for (genvar a=0; a<4; a++) begin : generate_tmr_in_assignments
			always_comb begin
				if (tmr_top.tmr_in[a] < 4'd10)
					tmr_in[a] = gpio_inputs[tmr_top.tmr_in[a]];
				else
					tmr_in[a] = 1'b0;
			end
		end
	endgenerate
	logic [3:0] tmr_in_sync[1:0];
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			for (int i=0; i<2; i++) begin
				tmr_in_sync[i] <= '0;
			end
		end
		else begin
			tmr_in_sync <= '{tmr_in_sync[0],tmr_in};
		end
	end
	
	generate
		for (genvar c=0; c<DSI_CHANNELS; c++) begin : generate_DSI3_tmr_in_assignments_to_dsi
			assign	tmr_dsi[c].tmr_in = tmr_in_sync[1]; 
		end
	endgenerate
	
	/*###   OTP   ######################################################*/
	logic	otp_ehv;
	assign	O_OTP_EHV = (atpgmode == 1'b1) ? 1'b0 : otp_ehv;
	assign	otp_io.a_ehv  = A_OTP_EHV ;
	//assign	A_OTP_VBG  = otp_io.a_vbg ;
	assign	A_OTP_VPP  = otp_io.a_vpp ;
	assign	A_OTP_VREF = otp_io.a_vref;
	assign	A_OTP_VRR  = otp_io.a_vrr ;
	assign	O_ATST_OTP	= (atpgmode == 1'b1) ? '0 : tmr_supply.tmr_ana_otp;
	

	/*###   logic top   ######################################################*/
    logic resb_scan_muxed;
    assign resb_scan_muxed = atpgmode ? supply_io.ldo_en : I_RESB;

`ifdef target_technology_FPGA
		logic_top i_logic_top (
				.\clk_rst_top\.clk  (clk_rst.clk),
				.\clk_rst_top\.rstn (clk_rst.rstn),
				.\spi_int\.sck      (spi_int.sck),
				.\spi_int\.sdi      (spi_int.sdi),
				.\spi_int\.csb      (spi_int.csb),
				.\spi_int\.csb_resn (spi_int.csb_resn),
				.\spi_int\.sdo      (spi_int.sdo),
				.\jtag\.tdo 	                  (jtag.tdo),
				.\jtag\.trstn 	                  (jtag.trstn),
				.\jtag\.tck 	                  (jtag.tck),
				.\jtag\.tdi 	                  (jtag.tdi),
				.\jtag\.tms 	                  (jtag.tms),
				.\jtag\.tmode                     (jtag.tmode ),
				.\dsi3_io[1]\.rx                  (dsi3_io[1].rx),
				.\dsi3_io[1]\.uv                  (dsi3_io[1].uv),
				.\dsi3_io[1]\.ov                  (dsi3_io[1].ov),
				.\dsi3_io[1]\.i_q				  (dsi3_io[1].i_q),
				.\dsi3_io[1]\.tx                  (dsi3_io[1].tx),
				.\dsi3_io[1]\.tx_hvcasc_on        (dsi3_io[1].tx_hvcasc_on),
				.\dsi3_io[1]\.tx_on               (dsi3_io[1].tx_on),
				.\dsi3_io[1]\.rx_on               (dsi3_io[1].rx_on),
				.\dsi3_io[1]\.receive_mode_enable (dsi3_io[1].receive_mode_enable),
				.\dsi3_io[1]\.trim_rx1            (dsi3_io[1].trim_rx1),
				.\dsi3_io[1]\.trim_rx2            (dsi3_io[1].trim_rx2),
				.\dsi3_io[1]\.bit_time            (dsi3_io[1].bit_time),
				.\dsi3_io[1]\.txd_shaped          (dsi3_io[1].txd_shaped),
				.\dsi3_io[1]\.short_filter_time   (dsi3_io[1].short_filter_time),
				.\dsi3_io[1]\.rx_idac 			  (dsi3_io[1].rx_idac),
				.\dsi3_io[0]\.rx                  (dsi3_io[0].rx),
				.\dsi3_io[0]\.uv                  (dsi3_io[0].uv),
				.\dsi3_io[0]\.ov                  (dsi3_io[0].ov),
				.\dsi3_io[0]\.i_q 				  (dsi3_io[0].i_q),
				.\dsi3_io[0]\.tx                  (dsi3_io[0].tx),
				.\dsi3_io[0]\.tx_hvcasc_on        (dsi3_io[0].tx_hvcasc_on),
				.\dsi3_io[0]\.tx_on               (dsi3_io[0].tx_on),
				.\dsi3_io[0]\.rx_on               (dsi3_io[0].rx_on),
				.\dsi3_io[0]\.receive_mode_enable (dsi3_io[0].receive_mode_enable),
				.\dsi3_io[0]\.trim_rx1            (dsi3_io[0].trim_rx1),
				.\dsi3_io[0]\.trim_rx2            (dsi3_io[0].trim_rx2),
				.\dsi3_io[0]\.bit_time            (dsi3_io[0].bit_time),
				.\dsi3_io[0]\.txd_shaped          (dsi3_io[0].txd_shaped),
				.\dsi3_io[0]\.short_filter_time   (dsi3_io[0].short_filter_time),
				.\dsi3_io[0]\.rx_idac  			  (dsi3_io[0].rx_idac),
				.\timebase_io\.clkref             (timebase_io.clkref),
				.\timebase_io\.clkpll             (timebase_io.clkpll),
				.\timebase_io\.clkpll_div         (timebase_io.clkpll_div),
				.\timebase_io\.clkref_div         (timebase_io.clkref_div),
				.\timebase_io\.pll_on             (timebase_io.pll_on),
				.\timebase_io\.pll_hold           (timebase_io.pll_hold),
				.\timebase_io\.trim_osc_f         (timebase_io.trim_osc_f),
				.\timebase_io\.trim_osc_tcf       (timebase_io.trim_osc_tcf),
				.\timebase_io\.pll_down_mon       (timebase_io.pll_down_mon),
				.\timebase_io\.pll_up_mon         (timebase_io.pll_up_mon),
				.\timebase_io\.pll_lock_mon       (timebase_io.pll_lock_mon),
				.\supply_io\.trim_iref            (supply_io.trim_iref),
				.\supply_io\.trim_ot              (supply_io.trim_ot),
				.\supply_io\.ldo_en               (supply_io.ldo_en),
				.\supply_io\.pad_drive_strength   (supply_io.pad_drive_strength),
				.\supply_io\.vcc_ok               (supply_io.vcc_ok),
				.\supply_io\.vrr_ok               (supply_io.vrr_ok),
				.\supply_io\.ldo_ok               (supply_io.ldo_ok),
				.\supply_io\.temp_warn            (supply_io.temp_warn),
				.\supply_io\.temp_error           (supply_io.temp_error),
				.\otp_io\.ehv                     (otp_io.ehv),
				.\otp_io\.otp_ready               (otp_io.otp_ready),
				.\otp_io\.a_ehv                   (otp_io.a_ehv),
				.\otp_io\.a_vbg                   (otp_io.a_vbg),
				.\otp_io\.a_vref                  (otp_io.a_vref),
				.\otp_io\.a_vrr                   (otp_io.a_vrr),
				.\otp_io\.a_vpp                   (otp_io.a_vpp),
				.\tmr_dsi[1]\.tmr_in              (tmr_dsi[1].tmr_in),
				.\tmr_dsi[1]\.tmr_ana_dsi3_tx     (tmr_dsi[1].tmr_ana_dsi3_tx),
				.\tmr_dsi[1]\.tmr_ana_dsi3_rx     (tmr_dsi[1].tmr_ana_dsi3_rx),
				.\tmr_dsi[0]\.tmr_in              (tmr_dsi[0].tmr_in),
				.\tmr_dsi[0]\.tmr_ana_dsi3_tx     (tmr_dsi[0].tmr_ana_dsi3_tx),
				.\tmr_dsi[0]\.tmr_ana_dsi3_rx     (tmr_dsi[0].tmr_ana_dsi3_rx),
				.\tmr_out_dsi[1]\.uv              (tmr_out_dsi[1].uv          ),
				.\tmr_out_dsi[1]\.ov              (tmr_out_dsi[1].ov          ),
				.\tmr_out_dsi[1]\.rx              (tmr_out_dsi[1].rx          ),
				.\tmr_out_dsi[1]\.rx_filtered     (tmr_out_dsi[1].rx_filtered ),
				.\tmr_out_dsi[1]\.icmp            (tmr_out_dsi[1].icmp        ),
				.\tmr_out_dsi[1]\.uv_synced       (tmr_out_dsi[1].uv_synced   ),
				.\tmr_out_dsi[1]\.ov_synced       (tmr_out_dsi[1].ov_synced   ),
				.\tmr_out_dsi[1]\.rx_synced       (tmr_out_dsi[1].rx_synced   ),
				.\tmr_out_dsi[1]\.icmp_synced     (tmr_out_dsi[1].icmp_synced ),
				.\tmr_out_dsi[1]\.value           (tmr_out_dsi[1].value       ),
				.\tmr_out_dsi[1]\.value_synced    (tmr_out_dsi[1].value_synced),
				.\tmr_out_dsi[0]\.uv              (tmr_out_dsi[0].uv          ), 
				.\tmr_out_dsi[0]\.ov              (tmr_out_dsi[0].ov          ), 
				.\tmr_out_dsi[0]\.rx              (tmr_out_dsi[0].rx          ), 
				.\tmr_out_dsi[0]\.rx_filtered     (tmr_out_dsi[0].rx_filtered ),
				.\tmr_out_dsi[0]\.icmp            (tmr_out_dsi[0].icmp        ),
				.\tmr_out_dsi[0]\.uv_synced       (tmr_out_dsi[0].uv_synced   ),
				.\tmr_out_dsi[0]\.ov_synced       (tmr_out_dsi[0].ov_synced   ),
				.\tmr_out_dsi[0]\.rx_synced       (tmr_out_dsi[0].rx_synced   ),
				.\tmr_out_dsi[0]\.icmp_synced     (tmr_out_dsi[0].icmp_synced ),
				.\tmr_out_dsi[0]\.value           (tmr_out_dsi[0].value       ),
				.\tmr_out_dsi[0]\.value_synced    (tmr_out_dsi[0].value_synced),
				.\tmr_osc\.tmr_ana_tb_pll         (tmr_osc.tmr_ana_tb_pll),
				.\tmr_osc\.tmr_ana_tb_osc         (tmr_osc.tmr_ana_tb_osc),
				.\tmr_out_osc\.clkref_filtered    (tmr_out_osc.clkref_filtered),
				.\tmr_out_osc\.clkref_divided     (tmr_out_osc.clkref_divided ),
				.\tmr_out_osc\.pll_down_mon       (tmr_out_osc.pll_down_mon   ),
				.\tmr_out_osc\.pll_up_mon         (tmr_out_osc.pll_up_mon     ),
				.\tmr_out_osc\.pll_lock_mon       (tmr_out_osc.pll_lock_mon   ),
				.\tmr_out_osc\.clkpll_div         (tmr_out_osc.clkpll_div     ),
				.\tmr_out_osc\.clkosc_divided     (tmr_out_osc.clkosc_divided ),
				.\tmr_out_osc\.clkpll_divided     (tmr_out_osc.clkpll_divided ),
				.\tmr_out_osc\.clksys_divided     (tmr_out_osc.clksys_divided ),
				.\tmr_out_osc\.clkosc             (tmr_out_osc.clkosc         ),
				.\tmr_out_osc\.clkpll             (tmr_out_osc.clkpll         ),
				.\tmr_out_osc\.clksys             (tmr_out_osc.clksys         ),
				.\tmr_out_osc\.clkref_ok          (tmr_out_osc.clkref_ok      ),
				.\tmr_out_osc\.pll_locked         (tmr_out_osc.pll_locked     ),
				.\tmr_out_osc\.clock_selected     (tmr_out_osc.clock_selected ),
				.\tmr_out_osc\.value              (tmr_out_osc.value          ),
				.\tmr_supply\.tmr_ana_supply      (tmr_supply.tmr_ana_supply),
				.\tmr_supply\.tmr_ana_temp_sensor (tmr_supply.tmr_ana_temp_sensor),
				.\tmr_supply\.tmr_ana_otp         (tmr_supply.tmr_ana_otp),
				.\tmr_scan\.scan                  (tmr_scan.scan),
				.\tmr_out_supply\.vcc_ok            (tmr_out_supply.vcc_ok           ),
				.\tmr_out_supply\.vrr_ok            (tmr_out_supply.vrr_ok           ),
				.\tmr_out_supply\.ldo_ok            (tmr_out_supply.ldo_ok           ),
				.\tmr_out_supply\.ot_error          (tmr_out_supply.ot_error         ),
				.\tmr_out_supply\.ot_warning        (tmr_out_supply.ot_warning       ),
				.\tmr_out_supply\.vcc_ok_synced     (tmr_out_supply.vcc_ok_synced    ),
				.\tmr_out_supply\.vrr_ok_synced     (tmr_out_supply.vrr_ok_synced    ),
				.\tmr_out_supply\.ldo_ok_synced     (tmr_out_supply.ldo_ok_synced    ),
				.\tmr_out_supply\.ot_error_synced   (tmr_out_supply.ot_error_synced  ),
				.\tmr_out_supply\.ot_warning_synced (tmr_out_supply.ot_warning_synced),
				.\tmr_out_supply\.value             (tmr_out_supply.value            ),
				.\tmr_out_supply\.value_synced      (tmr_out_supply.value_synced     ),
				.\tmr_scan\.scan_clock              (tmr_scan.scan_clock ),
				.\tmr_scan\.scan_reset              (tmr_scan.scan_reset ),
				.\tmr_scan\.scan                    (tmr_scan.scan       ),
				.\tmr_scan\.vdd_voltage_divider_disable (tmr_scan.vdd_voltage_divider_disable),
				.\tmr_scan\.vdd_disable             (tmr_scan.vdd_disable),
				.\tmr_scan\.vdd_load_disable        (tmr_scan.vdd_load_disable),
				.\tmr_scan\.disable_osc             (tmr_scan.disable_osc),
				.\tmr_top\.tmr_dig_use_jtag         (tmr_top.tmr_dig_use_jtag         ),
				.\tmr_top\.tmr_dig_sel_sync         (tmr_top.tmr_dig_sel_sync         ),
				.\tmr_top\.tmr_dig_ignore_osc_ready (tmr_top.tmr_dig_ignore_osc_ready ),
				.\tmr_top\.tmr_in[3]                (tmr_top.tmr_in[3]                ),
				.\tmr_top\.tmr_in[2]                (tmr_top.tmr_in[2]                ),
				.\tmr_top\.tmr_in[1]                (tmr_top.tmr_in[1]                ),
				.\tmr_top\.tmr_in[0]                (tmr_top.tmr_in[0]                ),
				.\tmr_top\.tmr_out_sel_sck          (tmr_top.tmr_out_sel_sck          ),
				.\tmr_top\.tmr_out_en_sck           (tmr_top.tmr_out_en_sck           ),
				.\tmr_top\.tmr_out_sel_csb          (tmr_top.tmr_out_sel_csb          ),
				.\tmr_top\.tmr_out_en_csb           (tmr_top.tmr_out_en_csb           ),
				.\tmr_top\.tmr_out_sel_miso         (tmr_top.tmr_out_sel_miso         ),
				.\tmr_top\.tmr_out_en_miso          (tmr_top.tmr_out_en_miso          ),
				.\tmr_top\.tmr_out_sel_mosi         (tmr_top.tmr_out_sel_mosi         ),
				.\tmr_top\.tmr_out_en_mosi          (tmr_top.tmr_out_en_mosi          ),
				.\tmr_top\.tmr_out_sel_syncb        (tmr_top.tmr_out_sel_syncb        ),
				.\tmr_top\.tmr_out_en_syncb         (tmr_top.tmr_out_en_syncb         ),
				.\tmr_top\.tmr_out_sel_bfwb         (tmr_top.tmr_out_sel_bfwb         ),
				.\tmr_top\.tmr_out_en_bfwb          (tmr_top.tmr_out_en_bfwb          ),
				.\tmr_top\.tmr_out_sel_intb         (tmr_top.tmr_out_sel_intb         ),
				.\tmr_top\.tmr_out_en_intb          (tmr_top.tmr_out_en_intb          ),
				.\tmr_top\.tmr_out_sel_dab          (tmr_top.tmr_out_sel_dab          ),
				.\tmr_top\.tmr_out_en_dab           (tmr_top.tmr_out_en_dab           ),
				.\tmr_top\.tmr_out_sel_rfc          (tmr_top.tmr_out_sel_rfc          ),
				.\tmr_top\.tmr_out_en_rfc           (tmr_top.tmr_out_en_rfc           ),
				.\tmr_top\.tmr_ana                  (tmr_top.tmr_ana                  ),
				.\dab_pad\.in_a                   (dab_pad.in_a),
				.\dab_pad\.in_s                   (dab_pad.in_s),
				.\dab_pad\.test_signal            (dab_pad.test_signal),
				.\dab_pad\.oe                     (dab_pad.oe),
				.\dab_pad\.ie                     (dab_pad.ie),
				.\dab_pad\.out                    (dab_pad.out),
				.\dab_pad\.pd                     (dab_pad.pd),
				.\dab_pad\.pu                     (dab_pad.pu),
				.\bfwb_pad\.in_a                  (bfwb_pad.in_a),
				.\bfwb_pad\.in_s                  (bfwb_pad.in_s),
				.\bfwb_pad\.test_signal           (bfwb_pad.test_signal),
				.\bfwb_pad\.oe                    (bfwb_pad.oe),
				.\bfwb_pad\.ie                    (bfwb_pad.ie),
				.\bfwb_pad\.out                   (bfwb_pad.out),
				.\bfwb_pad\.pd                    (bfwb_pad.pd),
				.\bfwb_pad\.pu                    (bfwb_pad.pu),
				.\rfc_pad\.in_a                   (rfc_pad.in_a),
				.\rfc_pad\.in_s                   (rfc_pad.in_s),
				.\rfc_pad\.test_signal            (rfc_pad.test_signal),
				.\rfc_pad\.oe                     (rfc_pad.oe),
				.\rfc_pad\.ie                     (rfc_pad.ie),
				.\rfc_pad\.out                    (rfc_pad.out),
				.\rfc_pad\.pd                     (rfc_pad.pd),
				.\rfc_pad\.pu                     (rfc_pad.pu),
				.\intb_pad\.in_a                  (intb_pad.in_a),
				.\intb_pad\.in_s                  (intb_pad.in_s),
				.\intb_pad\.test_signal           (intb_pad.test_signal),
				.\intb_pad\.oe                    (intb_pad.oe),
				.\intb_pad\.ie                    (intb_pad.ie),
				.\intb_pad\.out                   (intb_pad.out),
				.\intb_pad\.pd                    (intb_pad.pd),
				.\intb_pad\.pu                    (intb_pad.pu),
				.\syncb_pad\.in_a                 (syncb_pad.in_a),
				.\syncb_pad\.in_s                 (syncb_pad.in_s),
				.\syncb_pad\.test_signal          (syncb_pad.test_signal),
				.\syncb_pad\.oe                   (syncb_pad.oe),
				.\syncb_pad\.ie                   (syncb_pad.ie),
				.\syncb_pad\.out                  (syncb_pad.out),
				.\syncb_pad\.pd                   (syncb_pad.pd),
				.\syncb_pad\.pu                   (syncb_pad.pu),
				.i_clock_osc                      (clk_osc_scan_muxed     ),
				.i_resb                           (I_RESB          ),
				.i_por_n                          (I_PORB          ),
				.o_otp_ehv                        (otp_ehv));

	`else
		logic_top i_logic_top (
			.clk_rst_top      (clk_rst.master        ),
			.i_clock_osc      (clk_osc_scan_muxed    ),
			.i_resb           (resb_scan_muxed       ),
			.i_por_n          (I_PORB                ),
			.spi_int          (spi_int.slave         ),
			.dsi3_io          (dsi3_io[DSI_CHANNELS-1:0].master        ),
			.timebase_io      (timebase_io.master     ),
			.supply_io        (supply_io.master       ),
			.otp_io           (otp_io.master          ),
			.dab_pad          (dab_pad.master         ),
			.bfwb_pad         (bfwb_pad.master        ),
			.rfc_pad          (rfc_pad.master         ),
			.syncb_pad        (syncb_pad.master       ),
			.intb_pad         (intb_pad.master        ),
			.o_otp_ehv        (otp_ehv                ),
			.jtag             (jtag.slave             ),
			.tmr_osc          (tmr_osc.master         ),
			.tmr_out_osc      (tmr_out_osc.master     ),
			.tmr_supply       (tmr_supply.master      ),
			.tmr_out_supply   (tmr_out_supply.master  ),
			.tmr_dsi          (tmr_dsi.master         ),
			.tmr_out_dsi      (tmr_out_dsi.master     ),
			.tmr_scan         (tmr_scan.master        ),
			.tmr_top          (tmr_top.master         ));
	`endif

endmodule


