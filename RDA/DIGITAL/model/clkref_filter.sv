/**
 * Module: clkref_filter
 * 
 * analog CLKREF filter
 */
module clkref_filter (
		input	logic	CLKREF,
		output	logic	CLKREF_FILT
	);
	
	event	clkref_changed;
	
	always@(CLKREF) begin
		fork_clkref: fork
			begin
				#80ns;
				-> clkref_changed;
			end
			begin
				@(CLKREF);
			end
		join_any
		disable fork_clkref;
	end
	
	initial begin
		forever begin
			@(clkref_changed);
			CLKREF_FILT = CLKREF;
		end
	end

endmodule


