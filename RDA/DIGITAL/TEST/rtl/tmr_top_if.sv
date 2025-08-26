
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                Standard test module interface for TEST_TOP
 *==================================================*/
interface tmr_top_if;
	logic [3:0] tmr_in[3:0];

	logic  [5:0]	 tmr_out_sel_sck;
	logic  tmr_out_en_sck;
	logic  [5:0]	 tmr_out_sel_csb;
	logic  tmr_out_en_csb;
	logic  [5:0]	 tmr_out_sel_miso;
	logic  tmr_out_en_miso;
	logic  [5:0]	 tmr_out_sel_mosi;
	logic  tmr_out_en_mosi;
	logic  [5:0]	 tmr_out_sel_syncb;
	logic  tmr_out_en_syncb;
	logic  [5:0]	 tmr_out_sel_bfwb;
	logic  tmr_out_en_bfwb;
	logic  [5:0]	 tmr_out_sel_intb;
	logic  tmr_out_en_intb;
	logic  [5:0]	 tmr_out_sel_dab;
	logic  tmr_out_en_dab;
	logic  [5:0]	 tmr_out_sel_rfc;
	logic  tmr_out_en_rfc;
 	logic	tmr_ana;
	logic	tmr_dig_use_jtag;
	logic	tmr_dig_sel_sync;
	logic	tmr_dig_ignore_osc_ready;

	modport master (
		output	tmr_dig_use_jtag, tmr_dig_sel_sync, tmr_dig_ignore_osc_ready, 
		output	tmr_in,
		output	tmr_out_sel_sck, tmr_out_en_sck, tmr_out_sel_csb, tmr_out_en_csb, tmr_out_sel_miso, tmr_out_en_miso, tmr_out_sel_mosi, tmr_out_en_mosi, tmr_out_sel_syncb, tmr_out_en_syncb, tmr_out_sel_bfwb, tmr_out_en_bfwb, tmr_out_sel_intb, tmr_out_en_intb, tmr_out_sel_dab, tmr_out_en_dab, tmr_out_sel_rfc, tmr_out_en_rfc, 
 		output  tmr_ana
	);

	modport slave (
		input	tmr_dig_use_jtag, tmr_dig_sel_sync, tmr_dig_ignore_osc_ready, 
		input	tmr_in,
		input	tmr_out_sel_sck, tmr_out_en_sck, tmr_out_sel_csb, tmr_out_en_csb, tmr_out_sel_miso, tmr_out_en_miso, tmr_out_sel_mosi, tmr_out_en_mosi, tmr_out_sel_syncb, tmr_out_en_syncb, tmr_out_sel_bfwb, tmr_out_en_bfwb, tmr_out_sel_intb, tmr_out_en_intb, tmr_out_sel_dab, tmr_out_en_dab, tmr_out_sel_rfc, tmr_out_en_rfc, 
 		input  tmr_ana
	);

modport scanmux (
	input	tmr_ana 
);

	
endinterface
