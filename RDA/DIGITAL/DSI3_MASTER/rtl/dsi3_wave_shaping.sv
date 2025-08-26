/**
 * Module: dsi3_wave_shaping
 * 
 * Module for shaping the wave of the DSI3 output signal using a LUT
 */
module dsi3_wave_shaping  import dsi3_pkg::*; import project_pkg::*; #( // remove project package! 
		parameter DSI_COUNT = 2
		)(
			clk_reset_if.slave	clk_rst,
			jtag_bus_if.slave	jtag_bus,			
			input	logic[DSI_COUNT-1:0]	i_tx,
			input	dsi3_bit_time_e			i_tx_bit_time,
			output 	dsi3_tx_dac_t			o_tx_dac[DSI_COUNT-1:0]
		);
	
		
	`ifdef target_technology_FPGA
		generate
			for (genvar j=0; j<DSI_COUNT; j++) begin : o_tx_dac_assing
				always_comb	begin
					o_tx_dac[j][4] = i_tx[j];
				end
			end
		endgenerate
	`else

		
		/*###   LUT wave shape   ######################################################*/
		`include "dsi3_lut.sv"
		
		localparam int unsigned lut_size = $size(LUT[0]);
	
		
		/*###   wave shape generator   ######################################################*/
		typedef logic [$clog2(lut_size-1)-1:0] index_t;
					
		generate
			genvar i;
			for( i=0; i< DSI_COUNT; i++) begin : generate_wave_shape
				
				index_t index, index_nxt;
				dsi3_tx_dac_t dac, dac_nxt;
				
				always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
					if (clk_rst.rstn == 1'b0)  begin
						dac		<= '1;
						index	<= '0;
					end	else begin
						index	<= index_nxt;
						dac		<= dac_nxt;
					end
				end
						
				logic [1:0] div, div_nxt;
				always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
					if (clk_rst.rstn == 1'b0)  begin
						div		<= '0;
					end	else begin
						div		<= div_nxt;
					end
				end
				
				always_comb begin
					if ((index < index_t'(lut_size-1) && ~i_tx[i])  || (index > index_t'(0) && i_tx[i])) begin
						div_nxt = div - '1;
					end else begin
						div_nxt = '0;
					end
				end
				
				logic inc;
				always_comb begin
					case (i_tx_bit_time)
						BITTIME_16US: inc = div[0];
						BITTIME_32US: inc = &div;
						default : inc = '1;
					endcase
				end

				always_comb begin
					if (~i_tx[i]) begin
						if (index < index_t'(lut_size-1)) begin
							index_nxt = index + index_t'(inc);
						end else begin
							index_nxt = index_t'(lut_size-1);
						end
					end else begin
						if (index > index_t'(0)) begin
							index_nxt = index - index_t'(inc);
						end else begin
							index_nxt = '0;
						end
					end
				end
				
				assign dac_nxt = LUT [i_tx[i]] [index];
					
				test_ws #(
					.BASE_ADDR(BASE_ADDR_TEST_WS[i]),
					.ADDR_WIDTH(8)
				) i_test_ws (
					.jtag_bus(jtag_bus),					
					.i_DAC_tmr_val(dac),
					.o_DAC_tmr_val(o_tx_dac[i]),
					.o_jtag_dr()
				);
				
			end			
		endgenerate	
		
	`endif	// ifdef target_technology_FPGA
endmodule

