/**
 * Module: interface_converter_elip_bus_2_elip
 * 
 * converts elip_bus_if of UVM environment to elip_if of design (e.g. for registers)
 */
module interface_converter_elip_bus_2_elip #(parameter data_width=16)(
		clk_reset_if.slave	clk_rst,
		elip_bus_if			elip_bus,
		elip_if.master		elip,
		input logic[data_width-1:0] i_data_out
	);
	
	assign	elip_bus.clk = clk_rst.clk;
	assign	elip_bus.rstn = clk_rst.rstn;
	assign	elip_bus.data_read = i_data_out;
	assign	elip_bus.ready = 1'b1;
	assign	elip.addr = elip_bus.address;
	assign	elip.wr = elip_bus.write;
	assign	elip.rd = elip_bus.read;
	assign	elip.data_write = elip_bus.data_write;
	
endmodule


