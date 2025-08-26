/**
 * Interface: dsi3_io_if
 * 
 * interface containing all I/O signals to analog part of DSI3 block
 */
interface dsi3_io_if;
	import		dsi3_pkg::*;
	
	logic[1:0]	rx;
    logic       i_q; // quiescent current comparator input
	logic		uv;
	logic		ov;
	
	logic		tx_on;
	logic		tx_hvcasc_on;
	logic		rx_on;
	logic		receive_mode_enable;
	logic		tx;
	logic		short_filter_time;
    dsi3_rx_dac_t  rx_idac;
	
	dsi3_rx_trim_t	trim_rx1;
	dsi3_rx_trim_t	trim_rx2;
	
	dsi3_pkg::dsi3_tx_dac_t	txd_shaped;
	dsi3_bit_time_e			bit_time;
	
	
	modport master (
			input	rx, uv, ov, i_q,
			output	tx, tx_hvcasc_on, tx_on, rx_on, receive_mode_enable,
			output	trim_rx1, trim_rx2,
			output	bit_time, txd_shaped,
			output	short_filter_time,
			output	rx_idac
		);
	
	modport dsi3_block (
			input	rx, uv, ov, i_q,
			output	tx, tx_hvcasc_on, tx_on, rx_on, receive_mode_enable,
			output	trim_rx1, trim_rx2,
			output	rx_idac
		);

endinterface


