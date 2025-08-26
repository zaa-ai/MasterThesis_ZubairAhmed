/**
 * Interface: dsi3_common_config_if
 *
 * common configuration interface for DSI3 blocks
 */
interface dsi3_common_config_if;
	import project_pkg::*;
	import dsi3_pkg::*;

	dsi3_bit_time_e	bit_time;
	logic[1:0] 		chip_time;
	logic			crc_enable;
	logic			sync_pdcm;
	logic[6:0]		tx_shift;
	
	logic[10:0]		timeout_crm, timeout_crm_nr;

	modport slave (
			input	bit_time, chip_time, sync_pdcm, tx_shift
		);

	modport dsi3_block (
			input	bit_time, chip_time, crc_enable, sync_pdcm,
			input	timeout_crm, timeout_crm_nr
		);

endinterface


