/**
 * Module: interface_converter_elip_full_2_elip_bus
 * 
 * converts elip_full_if (from design) to elip_bus_if of UVM environment
 */
module interface_converter_elip_full_2_elip_bus(
		clk_reset_if.slave	clk_rst,
		elip_full_if.slave	elip_full,
		elip_bus_if			elip_bus
	);
	
	assign	elip_bus.address = elip_full.addr;
	assign	elip_bus.read = elip_full.rd;
	assign	elip_bus.write = elip_full.wr;
	assign	elip_bus.data_write = elip_full.data_write.data;
	assign	elip_bus.data_write_ecc = elip_full.data_write.ecc;
	assign	elip_bus.data_read = elip_full.data_read.data;
	assign	elip_bus.data_read_ecc = elip_full.data_read.ecc;
	assign	elip_bus.ready = elip_full.ready;
	assign	elip_bus.clk = clk_rst.clk;
	assign	elip_bus.rstn = clk_rst.rstn;

endmodule


