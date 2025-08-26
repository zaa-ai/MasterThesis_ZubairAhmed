`timescale 1ns/10ps

module IO_DIN_DIG #(parameter PullTime = 100000)
		(  output logic AOUT,
		output  C,
		input   DS,
		input   I,
		input   IE,
		input   OE,
		inout  PAD,
		input   PD,
		input   PU
	);

	wire   MG, PAD_i, C_buf, OEN, PAD_q, CO;
	
	reg lastPAD, pull_uen, pull_den, PS;
	
	bufif1 (weak0, weak1)(PAD_i, 1'b1, pull_uen);
	bufif1 (weak0, weak1)(PAD_i, 1'b0, pull_den); 
	buf    (C, CO);
	buf    (AOUT, CO);
	and    (CO, C_buf, IE);
	//nand   (PUEN, PS, PE);
	//not    (PU, PUEN);
	//not    (PSB, PS);
	//and    (PD, PE, PSB);
	not    (OEN, OE);
	bufif0 (PAD_q, I, OEN);
	pmos   (C_buf, PAD, 1'b0);
	pmos   (MG, PAD_q, 1'b0);
	pmos   (MG, PAD_i, 1'b0);
	pmos   (PAD, MG, 1'b0);
	
	initial begin
		pull_uen = 1'b0;
		pull_den = 1'b0;
		PS = 1'b0; //up
		//PS = 1; //down
	end
	
	always @(PAD)
		lastPAD=PAD;
	
	always @(PAD or PU or PD) begin
		if (PAD === 1'bx && !$test$plusargs("bus_conflict_off") && $countdrivers(PAD))
			$display("ERROR : %t ++BUS CONFLICT++ : %m", $realtime);
		if (PAD === 1'bz || (PAD === 1'b1) || (PAD === 1'b0)) begin
			if (PU) begin
				if (lastPAD === 1'b1) begin
					pull_uen = 1'b1;
					pull_den = 1'b0;
				end
				else begin
					pull_uen <= #PullTime 1'b1;
					pull_den <= #PullTime 1'b0;
				end
			end           
			else pull_uen = 1'b0;
			if (PD) begin
				if (lastPAD === 1'b0) begin
					pull_den = 1'b1; 
					pull_uen = 1'b0;
				end
				else begin
					pull_den <= #PullTime 1'b1;
					pull_uen <= #PullTime 1'b0;
				end
			end
			else pull_den = 1'b0;
		end 
	end
	specify
		if (DS == 1'b0) (I => PAD)=(0, 0);
		if (DS == 1'b1) (I => PAD)=(0, 0);
		if (DS == 1'b0) (OE => PAD)=(0, 0, 0, 0, 0, 0);
		if (DS == 1'b1) (OE => PAD)=(0, 0, 0, 0, 0, 0);
		(PAD => C)=(0, 0);
		(IE => C)=(0, 0);
	endspecify

endmodule
