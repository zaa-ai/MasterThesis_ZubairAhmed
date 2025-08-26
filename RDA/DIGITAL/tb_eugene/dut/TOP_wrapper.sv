`timescale 1ps/1ps

module TOP_WRAPPER import uvm_pkg::*; #(parameter DSI3_COUNT = 2)
	( 
		// SPI
		input	wire	MOSI_P,
		output	wire	MISO_P,
		input	wire	SCK_P,
		input	wire	CSB_P,
		        
		output	wire	INTB_P,
		output	wire	RFC_P,
		output	wire	DAB_P,
		output	wire	BFWB_P,
		
		input	wire	SYNCB_P,
		output	wire	SYNCB_OUT_P,
		
		// JTAG
		input	logic	TDI_P,
		output	logic	TDO_P,
		input	logic	TCK_P,
		input	logic	TMS_P,		
				
		input 	logic	CLKREF_P,
		output	logic	CLKREF_EN_P,
		output 	real	AOUT_P,
		
		input	logic	TMODE_P,
		input	logic	RESB_P,	
		//DSI
		dsi3_slave_if	DSI_P[DSI3_COUNT-1:0],
		
		input	real	VSUP_P,
		output	real	VCC_P,
		output	real	VDD18_P,
		output	real	LDO_P,
		input	real	TEMP,
    	real_signal_if  ILOAD[DSI3_COUNT-1:0]
	);
	
	logic	enable_pattern = 1'b0;
	string current_sequence = "none";

	/*
	 * RFC		TDO
	 * DAB		TMS
	 * BFWB		TCK
	 * SYNCB	TDI
	 * */
	wire rfc_tdo, bfwb_tck, dab_tms, syncb_tdi;
	wire	intb_tdo;
	
	assign	`xana_path.temperature	= TEMP;
	
	/*###   OTP interface   #################################################*/
	OTP_model_if OTP_model_if_inst();
`ifndef target_technology_FPGA
	always @(OTP_model_if_inst.dat_file) begin
		`OTP_INST.readOtp(2048'(OTP_model_if_inst.dat_file));
	end
`endif

	/*###   sequence interface   #################################################*/
	sequence_if sequence_if_inst();
	always @(sequence_if_inst.sequence_count) begin
		current_sequence = sequence_if_inst.current_sequence;
	end
	
	clk_osc_if clk_osc_if_inst();
	
	initial begin
		uvm_config_db#(virtual OTP_model_if)::set(null, "*", "OTP_model_if_inst", OTP_model_if_inst);
		uvm_config_db#(virtual sequence_if)::set(null, "*", "sequence_if_inst", sequence_if_inst);
		uvm_config_db#(virtual clk_osc_if)::set(null, "*", "clk_osc_if_inst", clk_osc_if_inst);
	end
	
	/*###   interface mapping   ######################################################*/
	real dsi3_real[DSI3_COUNT-1:0];
	
	/*###   JTAG switching   ######################################################*/
	tran (DAB_P, dab_tms);
	tran (BFWB_P, bfwb_tck);
	pmos (syncb_tdi, SYNCB_P, TMODE_P);
    tran (SYNCB_OUT_P, syncb_tdi);
	
	nmos(dab_tms,   TMS_P, TMODE_P & ~enable_pattern);		//TODO: use pull down and up to drive signal instead of muxing!
	nmos(bfwb_tck,  TCK_P, TMODE_P & ~enable_pattern);
	nmos(syncb_tdi, TDI_P, TMODE_P & ~enable_pattern);
	
	import	M52144A_pattern_pkg::*;
	initial begin
		#1;
		uvm_config_db#(M52144A_pattern_wrapper)::set(null, "*", "pattern_wrapper", i_p52144_pattern.wrapper);
	end

	wire DAB_PIN, SYNCB_PIN, BFWB_PIN;
	
	M52144A_pattern i_p52144_pattern (
		.DAB_TMS_MDMA_DPIN    (DAB_PIN   ), 
		.SYNCB_TDI_MDMA_DPIN  (SYNCB_PIN ), 
		.BFWB_TCK_MDMA_DPIN   (BFWB_PIN  ), 
		.INTB_TDO_MDMA_DPIN   (intb_tdo   ));

	nmos(dab_tms,   DAB_PIN, enable_pattern);
	nmos(bfwb_tck,  BFWB_PIN, enable_pattern);
	nmos(syncb_tdi, SYNCB_PIN, enable_pattern);
	
	pulldown(SYNCB_P);
	pullup(DAB_P);
	pullup(BFWB_P);
	
	assign TDO_P	= (TMODE_P == 1) ? intb_tdo : 1'bz;
	assign INTB_P   = intb_tdo;
	assign RFC_P	= rfc_tdo;
	
	`ifdef GATE_LEVEL
	assign clk_osc_if_inst.clk = xtop.CLKOSC;
	`endif	
	
	real GND;
	assign GND=0.0;
	assign CLKREF_EN_P = 1'b1;
	
	TOP #(
		.DSI3_COUNT  (DSI3_COUNT )
	) xtop (
		.MOSI_P      (MOSI_P     ), 
		.MISO_P      (MISO_P     ), 
		.SCK_P       (SCK_P      ), 
		.CSB_P       (CSB_P      ), 
		.INTB_P      (intb_tdo   ), 
		.RFC_P       (rfc_tdo    ), 
		.DAB_P       (dab_tms    ), 
		.BFWB_P      (bfwb_tck   ), 
		.SYNCB_P     (syncb_tdi  ), 
		.CLKREF_P    (CLKREF_P   ), 
		.AOUT_P      (AOUT_P     ), 
		.DGND_P      (GND        ), 
		.DSI_P       (dsi3_real  ), 
		.LDO_P       (LDO_P      ), 
		.VSUP_P      (VSUP_P     ), 
		.GNDA_P      (GND        ), 
		.VCC_P       (VCC_P      ), 
		.GNDD_P      (GND        ), 
		.VDD18_P     (VDD18_P    ), 
		.TMODE_P     (TMODE_P    ), 
		.RESB_P      (RESB_P     )
	);
	
	generate
		genvar k;
		for (k=0; k<DSI3_COUNT; k++) begin : generate_receiver_outputs
			
			dsi3_signal_converter_digital #(.channel_index(k)) i_dsi3_signal_converter
				(
					.DSI(dsi3_real[k]), 
					.VDSI(LDO_P),
					.ILOAD(ILOAD[k].PIN),
					.cable_if(DSI_P[k])
				);				
		end
	endgenerate
		
endmodule //TOP_WRAPPER
`resetall
