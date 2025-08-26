/**
 * Interface: tmr_out_supply_if
 * 
 * interface for digital outputs via TMR_OUT of supply block
 */
interface tmr_out_supply_if;
	logic	vcc_ok, vrr_ok, ldo_ok, ot_error, ot_warning;
	logic	vcc_ok_synced, vrr_ok_synced, ldo_ok_synced, ot_error_synced, ot_warning_synced;
	
	logic[4:0]	value, value_synced;

	modport master(
		output	vcc_ok, vrr_ok, ldo_ok, ot_error, ot_warning,
		output	vcc_ok_synced, vrr_ok_synced, ldo_ok_synced, ot_error_synced, ot_warning_synced
	);
	
	modport slave (
		input	value, value_synced
	);
	
	assign	value = {vrr_ok, ldo_ok, vcc_ok, ot_error, ot_warning};
	assign	value_synced = {vrr_ok_synced, ldo_ok_synced, vcc_ok_synced, ot_error_synced, ot_warning_synced};
endinterface


