/**
 * Module: supply
 * 
 * model of analog supply
 */
module supply_top(
		input	real	AGND,
		input	real	VSUP,
		input 	real	VDD1V8_sense,
		input	logic	REG_DIS,

		output	logic	PORB,
		output	real	VDD1V8,
		output	real	VCC,
		output	logic	VCC_OK
	);

	initial begin
		PORB <= 1'b0;
		VCC_OK <= 1'b0;
	end
	
	///*###   POR Generation   ######################################################*/
	always @(*)	begin : PORB_gen
		if ((VDD1V8_sense - AGND) > 1.5)
			PORB <= 1'b1;
		else if ((VDD1V8_sense - AGND) < 1.4 )
			PORB <= 1'b0;
	end
	
	///*###   VCC_UV Generation   ######################################################*/
	always @(*)
	begin : VCC_OK_gen
		if((VCC - AGND) < 4.3)
			VCC_OK <= 1'b0;
		else if ((VCC - AGND) > 4.5)
			VCC_OK <= 1'b1;
	end
	
	///*###   VCC Regulator   ######################################################*/
	always @(*) begin
		if ((VSUP - AGND) < 5.0)
			VCC = VSUP;
		else
			VCC = 5.0;
	end
	
	///*###   VDD Regulator   ######################################################*/
	always @(*) begin
		if (REG_DIS == 1'b0) begin
			begin
				if ((VCC - AGND) < 2.8)
					VDD1V8 = VCC - 1.0;
				else
					VDD1V8 = 1.8;
			end	
		end /* if (REG_DIS == 1'b0) */
		else begin
			VDD1V8 = 0.0;
		end
	end
	
endmodule


