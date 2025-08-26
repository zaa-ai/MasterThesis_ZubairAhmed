
module dsi3_signal_converter_mixed #(
		parameter channel_index = 0
	)(
		inout DSI,
		input real VSUP,
		dsi3_slave_if	cable_if
	);
	
	real DSI_v;
	real DSI_i;
	parameter real DSI_i_quiet = 1.0e-3;
	
	real VSUP_v;
	real VSUP_i;
	
	
	always_comb begin
	
		if (VSUP >= 3.0) begin
			if ((VSUP - 1.0) > DSI_v)
				cable_if.cable.Voltage = 1'b0;
			else
				cable_if.cable.Voltage = 1'b1;
		end
		else
			cable_if.cable.Voltage = 1'b1;
			
	end
	
	
	always_comb begin
		if (cable_if.cable.Current == 0) begin
			DSI_i = DSI_i_quiet;
		end
		else if (cable_if.cable.Current == 1) begin
			DSI_i = 12.0e-3 + DSI_i_quiet;
		end
		else begin
			DSI_i = 24.0e-3 + DSI_i_quiet;
		end
		VSUP_i = 0.0;
	end
	
	e2r_iin_vout i_e2r_dsi(
		.a    (DSI),
		.vout (DSI_v),
		.iin  (DSI_i));
//	
//	e2r_iin_vout i_e2r_vsup(
//		.a    (VSUP),
//		.vout (VSUP_v),
//		.iin  (VSUP_i));
		
endmodule


