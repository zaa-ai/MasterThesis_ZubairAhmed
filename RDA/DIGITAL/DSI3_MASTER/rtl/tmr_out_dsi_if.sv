/**
 * Interface: tmr_out_dsi_if
 * 
 * interface for digital outputs via TMR_OUT of DSI3 block
 */
interface tmr_out_dsi_if;
	logic	uv, ov, icmp;
	logic[1:0]	rx;
	logic[1:0]	rx_filtered;
	logic	uv_synced, ov_synced, icmp_synced;
	logic[1:0]	rx_synced;
	
	logic[4:0]	value, value_synced;
	
	modport master (
			output	uv, ov, rx, rx_filtered, icmp,
			output	uv_synced, ov_synced, rx_synced, icmp_synced
		);
	
	modport slave (
			input	value, value_synced
		);
	
	assign	value = {icmp, ov, uv, rx};
	assign	value_synced = {icmp_synced, ov_synced, uv_synced, rx_synced};

endinterface


