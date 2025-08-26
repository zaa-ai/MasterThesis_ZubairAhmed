
/*==================================================
 *  Copyright (c) 2023 Elmos SE
 *  Author: stove
 *  Description : Note: This file has been generated automatically by stove
 *                Note: This file should not be modified manually.
 *                test interface definition for TEST_SUPPLY
 *==================================================*/
interface tmr_supply_if;

	logic	[4:0] tmr_ana_supply;
	logic	[1:0] tmr_ana_temp_sensor;
	logic	[5:0] tmr_ana_otp;


modport master (
 		output  tmr_ana_supply,
 		output  tmr_ana_temp_sensor,
 		output  tmr_ana_otp
);

modport slave (
 		input  tmr_ana_supply,
 		input  tmr_ana_temp_sensor,
 		input  tmr_ana_otp
);

modport iomux (
 		output  tmr_ana_supply,
 		output  tmr_ana_temp_sensor,
 		output  tmr_ana_otp
);


modport scanmux (
	input   tmr_ana_supply,  tmr_ana_temp_sensor,  tmr_ana_otp  
);

endinterface
