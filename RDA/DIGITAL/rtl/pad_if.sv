
`timescale 1ns/1ns

interface pad_if;

	logic  in_a;	// syncronized signal
	logic  oe;	// out enable	
	logic  out;	// output
	logic  pd; 	// pull down enable
	logic  pu; 	// pull up enable

	modport master(
			input  in_a,
			output oe,
			output out,
			output pd,
			output pu
		);

	modport slave(
			output in_a,
			input  oe,
			input  out,
			input  pd,
			input  pu
		);


	`ifdef SVA

		always_comb
		begin
			if ($time > 0) begin
				//in_never_x  : assert (!$isunknown(in))  else $error;
				in_never_x : assert (!$isunknown(in)) else $fatal;
				oe_never_x  : assert (!$isunknown(oe))  else $fatal;
				out_never_x  : assert (!$isunknown(out))  else $fatal;
				pd_never_x : assert (!$isunknown(pd)) else $fatal;
				pu_never_x : assert (!$isunknown(pu)) else $fatal;
			end
		end

	`endif

endinterface

