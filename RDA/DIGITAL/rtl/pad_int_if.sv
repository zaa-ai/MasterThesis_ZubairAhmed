
interface pad_int_if;

	logic  in_a;	// asyncrounos signal
	logic  in_s;	//  syncrounos signal
	logic  test_signal; // testsignal after first syncronization flip flop
	logic  oe;	// out enable	
	logic  ie;	// input enable	
	logic  out;	// output
	logic  pd; 	// pull down enable
	logic  pu; 	// pull up enable

	modport master(
			input  in_a,
			input  in_s,
			input  test_signal,
			output oe,
			output ie,
			output out,
			output pd,
			output pu
		);

	modport slave(
			output in_a,
			input  oe,
			input  ie,
			input  out,
			input  pd,
			input  pu
		);
	
	modport sync(
			input  in_a,
			output in_s,
			output test_signal,
			input  oe,
			input  ie,
			input  out,
			input  pd,
			input  pu
		);
	
	modport use_signals(
			input  in_a,
			input  in_s,
			input  test_signal,
			input  oe,
			input  ie,
			input  out,
			input  pd,
			input  pu			
		);

	`ifdef SVA

		always_comb
		begin
			if ($time > 0) begin
				in_never_x : assert (!$isunknown(in_s)) else $fatal;
				oe_never_x  : assert (!$isunknown(oe))  else $fatal;
				out_never_x  : assert (!$isunknown(out))  else $fatal;
				pd_never_x : assert (!$isunknown(pd)) else $fatal;
				pu_never_x : assert (!$isunknown(pu)) else $fatal;
			end
		end

	`endif

endinterface

