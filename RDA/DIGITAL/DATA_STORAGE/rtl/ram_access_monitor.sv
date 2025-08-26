/**
 * Module: ram_access_monitor
 * 
 * TODO: Add module documentation
 */
module ram_access_monitor (
		clk_reset_if.slave	clk_rst,
		input	logic	read,
		input	logic	write
	);
	
	logic	access = read | write;
	
	bit[9:0]	access_10;
	bit[19:0]	access_20;
	bit[99:0]	access_100;
	
	int counter_10, counter_20, counter_100;
	
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			access_10 <= '0;
			access_20 <= '0;
			access_100 <= '0;
		end
		else begin
			access_10 <=  {access_10[8:0], access};
			access_20 <=  {access_20[18:0], access};
			access_100 <= {access_100[98:0], access};
		end
	end
	
	assign	counter_10 = $countones(access_10);
	assign	counter_20 = $countones(access_20);
	assign	counter_100 = $countones(access_100);
	
	always@(posedge clk_rst.clk) begin
		if(access_10 > 8) begin
			$warning("RAM load is > 80%%");
		end
		if(access_20 > 8) begin
			$error("RAM load is > 80%%");
		end
		if(access_100 > 8) begin
			$fatal("RAM load is > 80%%");
		end
	end
	
endmodule


