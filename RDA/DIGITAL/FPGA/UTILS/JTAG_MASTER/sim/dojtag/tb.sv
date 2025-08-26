
module tb();

	logic rstn, clk, tick, soc, eoc;
	logic tck, tdi, tms, trstn, tdo;
	logic clock_dr, shift_dr, update_dr;

	`include "dojtag_inc.sv"
	t_irdr irdr;

	//JTAG+TAP MASTER
	dojtag xdojtag(.*);

	//TAP SLAVE
	DW_tap #(
			.width(8), .id(0), .version(0), .part(52143), .man_num({3'b000, 8'h45, 1'b1}),	.sync_mode(0), .tst_mode(1))
		xtap (
			.trst_n(trstn), .so('0), .bypass_sel('0), .sentinel_val('0), .tdo_en(),
			.tap_state(), .extest(), .samp_load(), .sync_capture_en(), .sync_update_dr(),
			.test('0), .instructions(irdr.ir), .*);

	//JTAG DR
	always_ff @(negedge trstn or posedge tck iff trstn) begin
		if (!trstn) begin
			irdr.dr <= '0;
		end else begin
			if (shift_dr) begin
				irdr.dr <= {tdi, irdr.dr[`dr_length - 1 :1]};
			end
		end
	end

	//CLOCK
	initial begin
		rstn = '0;
		clk = '0;
		tick =  '0;
		#(1us);
		rstn = '1;
		#(1us);
		forever begin
			#(1us) clk = ~clk;
			#(1us) clk = ~clk;
			tick = ~ tick;
		end
	end



	//start conversion and check ir & dr at end
	initial begin
		soc = '0;
		@(posedge trstn);
		soc = '1;
		@(negedge eoc);
		soc = '0;
		//		foreach (mem[i]) begin // this results in mem[i] = 'hxxxxxx
		for (int i=1;i>-1;i--) begin
			@(posedge update_dr);
			assert (mem[i] == irdr) else $error("IR/DR mismatch %h $%h",mem[i],irdr);
		end
		@(posedge eoc);
		$finish();
	end


endmodule
