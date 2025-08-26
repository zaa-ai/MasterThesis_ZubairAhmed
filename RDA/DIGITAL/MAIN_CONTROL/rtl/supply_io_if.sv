/**
 * Interface: supply_io_if
 * 
 * interface containing all I/O signals to analog part of supply block
 */
interface supply_io_if;
	import project_pkg::*;
	logic[TRIM_IREF_WIDTH-1:0]	trim_iref;
	logic[1:0]	trim_ot;
	logic	vcc_ok;
	logic	vrr_ok;
	logic	ldo_en;
	logic	ldo_ok;
	logic	temp_warn;
	logic	temp_error;
	logic	pad_drive_strength;
	
	modport slave(
			input	trim_iref, trim_ot, ldo_en, pad_drive_strength,
			output	vcc_ok, vrr_ok, ldo_ok, temp_warn, temp_error
		);
	
	modport master(
			output	trim_iref, trim_ot, ldo_en, pad_drive_strength,
			input	vcc_ok, vrr_ok, ldo_ok, temp_warn, temp_error
		);

endinterface


