/**
 * Module: elip_splitter
 *
 * module for splitting ELIP busses
 */
module elip_splitter #(
		parameter	interfaces = 2
	)(
		elip_full_if.slave	elip_master,
		elip_full_if.master	elip_slave[interfaces-1:0]
	);
	import project_pkg::*;

	data_ecc_t	data_read[interfaces-1:0];

	generate
		genvar i;
		for (i = 0; i<interfaces; i++) begin : generate_elip_connections
			assign	elip_slave[i].addr = elip_master.addr;
			assign	elip_slave[i].data_write = elip_master.data_write;
			assign	elip_slave[i].rd = elip_master.rd;
			assign	elip_slave[i].wr = elip_master.wr;
			assign	data_read[i] = elip_slave[i].data_read;
		end
	endgenerate

	elip_data_t data;
	always_comb begin
		data = '0;
		for (int k=0; k<interfaces; k++)
			data |= data_read[k];
		elip_master.data_read = data;
	end

endmodule


