/**
 * Module: dsi3_signal_converter_digital
 * 
 * module for converting dsi3 signals
 */
`define transceiver_path 		top_tb.th.i_dut_wrapper.xtop.XANA.gen_dsi_trx

module dsi3_signal_converter_digital #(
		parameter channel_index = 0
	)(
		input real	DSI,
		input real	VDSI,
		input real	ILOAD,
		dsi3_slave_if	cable_if
	);
	
	always_comb begin
		if (VDSI > 0.0) begin
            if (cable_if.cable.Voltage == 1'b1) begin
                if (DSI < (VDSI-1.1 - 1.09))
    				cable_if.cable.Voltage = 1'b0;
                else
    				cable_if.cable.Voltage = 1'b1;
            end
            else begin
    			if (DSI > (VDSI-1.05 - 1.0))
    				cable_if.cable.Voltage = 1'b1;
                else
    				cable_if.cable.Voltage = 1'b0;
            end
		end
		else
			cable_if.cable.Voltage = 1'b0;
	end
	
	assign	`transceiver_path[channel_index].i_dsi_transceiver.iload = cable_if.cable.Current * 12.0 + ILOAD;
		
endmodule
