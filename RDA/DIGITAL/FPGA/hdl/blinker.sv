
`timescale 1ns/10ps

module blinker #(
		parameter SYS_FREQ_KHZ = 18000,  // TODO use this -> make blinker sys freq adjustable
		parameter WITH_NRES_SYNC  = 1,
		parameter WITH_OBUF       = 1
		)(
		input          clk,
		input          nrst,
		output  [1:0]  leds
		);

	logic [1:0] leds_int;

	generate
		if (WITH_OBUF == 1) begin
			OBUF OBUF_leds[1:0](.I(leds_int), .O(leds));
		end
		else begin
			assign leds = leds_int;
		end
	endgenerate

	logic nreset;

	generate
		if (WITH_NRES_SYNC == 1) begin
			utils_reset_sync utils_reset_sync_inst(
					.clk         (clk),
					.i_nrst      (nrst),
					.o_nrst      (nreset),
					.i_scan_mode (1'b0)
				);
		end
		else begin
			assign nreset = nrst;
		end
	endgenerate

	logic led_num;
	logic up;
	logic [22:0]  counter;

	always_comb
	begin
		if (counter[9:4] < counter[22:17]) begin
			if (led_num == 1'b1) begin
				leds_int[1:0] = 2'b01;
			end
			else begin
				leds_int[1:0] = 2'b10;
			end
		end
		else begin
			leds_int[1:0] = 2'b11;
		end
	end

	always @(negedge nreset or posedge clk)
	begin
		if (!nreset) begin
			up <= 1'b1;
			counter <= 'h0;
			led_num <= 1'b1;
		end
		else
		begin
			if (up == 1'b1) begin
				if (counter == 'h7fffff) begin
					up <= 1'b0;
				end
				else begin
					counter <= counter + 'h1;
				end
			end
			else
			if (counter == 'h0) begin
				up <= 1'b1;
				led_num <= ~led_num;
			end
			else begin
				counter <= counter - 'h1;
			end
		end
	end

endmodule

