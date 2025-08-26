`timescale 1s/1fs


module dsi3_signal_converter_mixed #(
		parameter channel_index = 0
	)(
		inout DSI,
		inout VSUP,
		
		input  [1:0] cable_if_i,
		output cable_if_v
	);
	
	
	reg cable_if_v;
	
	real DSI_v;
	real DSI_i;
	parameter real DSI_i_quiet = 1.0e-3;
	
	real VSUP_v;
	real VSUP_i;
	
	
	always @(*) begin
		if (VSUP_v >= 3.0) begin
			if ((VSUP_v - 1.0) > DSI_v)
				cable_if_v = 1'b0;
			else
				cable_if_v = 1'b1;
		end
		else
				cable_if_v = 1'b1;
	end
	
	
	always @(*) begin
	
		if (cable_if_i > 0) begin
			if (cable_if_i > 2) begin
		  		DSI_i = 24.0e-3 + DSI_i_quiet;
			end
			else begin
		  		DSI_i = 12.0e-3 + DSI_i_quiet;
			end
		end
		else begin
		  	DSI_i = DSI_i_quiet;
		end
		
		VSUP_i = 0.0;
	end
	
	e2r_iin_vout i_e2r_dsi(
		.a    (DSI),
		.vout (DSI_v),
		.iin  (DSI_i));
	
	e2r_iin_vout i_e2r_vsup(
		.a    (VSUP),
		.vout (VSUP_v),
		.iin  (VSUP_i));
		
endmodule




module dsi3_signal_converter_mixed_tb (
			output  [1:0] cable_if_i,
			input cable_if_v
	);
	
	
	reg [1:0] cable_if_i;
	
	initial begin
	
	  cable_if_i = 1;
	  #(4.0e-3);
	  
	  cable_if_i = 2;
	  #(1.0e-3);
	  
	  cable_if_i = 3;
	  #(1.0e-3);
	  
	  cable_if_i = 0;
	  #(1.0e-3);
	  
	end
		
endmodule


