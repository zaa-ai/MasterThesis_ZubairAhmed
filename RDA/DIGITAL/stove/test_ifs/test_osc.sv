
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                test interface definition for TEST_OSC
 *==================================================*/
interface tmr_osc_if;

	logic	[6:0] tmr_ana_tb_pll;
	logic	[2:0] tmr_ana_tb_osc;


modport master (
 		output  tmr_ana_tb_pll,
 		output  tmr_ana_tb_osc
);

modport slave (
 		input  tmr_ana_tb_pll,
 		input  tmr_ana_tb_osc
);

modport iomux (
 		output  tmr_ana_tb_pll,
 		output  tmr_ana_tb_osc
);


modport scanmux (
	input   tmr_ana_tb_pll,  tmr_ana_tb_osc  
);

endinterface
