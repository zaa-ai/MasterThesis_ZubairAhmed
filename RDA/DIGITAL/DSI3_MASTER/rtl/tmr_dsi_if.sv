

/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                test interface definition for TEST_DSI
 *==================================================*/
interface tmr_dsi_if;

	logic	[3:0] tmr_in;
	logic	[6:0] tmr_ana_dsi3_tx;
	logic	[0:0] tmr_ana_dsi3_rx;


modport master (
		input	tmr_in,
 		output  tmr_ana_dsi3_tx,
 		output  tmr_ana_dsi3_rx
);

modport slave (
		output	tmr_in,
 		input  tmr_ana_dsi3_tx,
 		input  tmr_ana_dsi3_rx
);

modport iomux (
		output	tmr_in,
 		output  tmr_ana_dsi3_tx,
 		output  tmr_ana_dsi3_rx
);


modport scanmux (
	input   tmr_ana_dsi3_tx,  tmr_ana_dsi3_rx  
);

endinterface
