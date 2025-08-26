/**
 * Module: tdma_spi_reader_demux
 *
 * Demultiplexing a buffer reader interface array
 */
module tdma_spi_reader_demux import project_pkg::*; import buffer_if_pkg::*; (
		tdma_spi_reader_if.slave 	reader,
        tdma_spi_reader_if.master	readers[DSI_CHANNELS-1:0],
		input	dsi_select_t	channel_select
	);

	data_ecc_t	data[DSI_CHANNELS-1:0];
	logic	ready[DSI_CHANNELS-1:0];
	logic	empty[DSI_CHANNELS-1:0];

	generate
		for(genvar i=0; i < DSI_CHANNELS; i++) begin : generate_interface_connections
			assign	readers[i].action = (channel_select == dsi_select_t'(i)) ? reader.action : IDLE_READ;
			assign	readers[i].step = reader.step;

			assign	data[i] = readers[i].data;
			assign	ready[i] = readers[i].ready;
			assign	empty[i] = readers[i].empty;
		end
	endgenerate

	assign	reader.data		= (int'(channel_select) < DSI_CHANNELS) ? data[channel_select] : '0;
	assign	reader.empty	= (int'(channel_select) < DSI_CHANNELS) ? empty[channel_select]: '1;
	assign	reader.ready	= (int'(channel_select) < DSI_CHANNELS) ? ready[channel_select]: '1;

endmodule


