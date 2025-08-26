module debounce
	#(initVal = 8, 
	  resVal = 0,
	  dir = 2,
	  sync = 1)
	(output logic out,
	 input  logic in,
	 input  logic clk,
	 input  logic resn);
	
	logic [$clog2(initVal-1)-1:0] cnt;
	logic sync1;

	if (sync) 
	begin
		logic sync0;
		always_ff @(posedge clk, negedge resn)
			if (!resn) 
			begin
				sync1 <= resVal;
				sync0 <= resVal;
			end
			else
			begin 
				sync1 <= sync0;
				sync0 <= in;
			end
	end
	else
	begin
		always_comb @(in)
			sync1 <= in;
	end
	
	if (dir == 2)
	begin
		always_ff @(posedge clk, negedge resn)
			if (!resn) 
				begin
					out <= resVal;
					cnt <= initVal-1;
				end
			else if (sync1 != out)
				begin
					if (cnt == 0)
						begin
							cnt <= initVal-1;
							out <= sync1;
						end
					else
						cnt <= cnt - 1;				
				end
			else
				cnt <= initVal-1;
	end
	else if (dir==1)
	begin
		always_ff @(posedge clk, negedge resn)
			if (!resn) 
				begin
					out <= resVal;
					cnt <= initVal-1;
				end
			else if (in)
				begin
					if (cnt == 0)
						begin
							cnt <= initVal-1;
							out <= sync;
						end
					else
						cnt <= cnt - 1;				
				end
			else
				cnt <= initVal-1;
				out <= sync;
	end
	else
	begin
		always_ff @(posedge clk, negedge resn)
			if (!resn) 
				begin
					out <= resVal;
					cnt <= initVal-1;
				end
			else if (!in)
				begin
					if (cnt == 0)
						begin
							cnt <= initVal-1;
							out <= sync;
						end
					else
						cnt <= cnt - 1;				
				end
			else
				cnt <= initVal-1;
				out <= sync;
	end

//	assert_deb #() xassert ();	 
	 
endmodule

