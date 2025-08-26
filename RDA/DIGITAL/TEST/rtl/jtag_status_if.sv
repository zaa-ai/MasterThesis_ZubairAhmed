/**
 * Interface: jtag_status_if
 * 
 * Bus to attach JTAG test blocks to
 */
interface jtag_status_if;
	
	// latched instruction from TAP
	jtag_pkg::t_jtag_isr ir;
	
	// Data-Shift-Register control and data
	jtag_pkg::t_jtag_dsr dsr;
	
	// JTAG tap states (unlatched)
	logic test_rst;
	logic run_idle;
	logic capture_dr;
	logic shift_dr;
	logic update_dr;
	logic update_ir;
	
	// JTAG tap states (latched -> falling edge of tck)
	logic test_rst_fe;
	logic run_idle_fe;
	logic capture_dr_fe;
	logic shift_dr_fe;
	logic update_dr_fe;
	logic update_ir_fe;
	
	modport master (
			output	ir, dsr, test_rst, run_idle, capture_dr, shift_dr, update_dr, update_ir, 
			output	test_rst_fe, run_idle_fe, capture_dr_fe, shift_dr_fe, update_dr_fe, update_ir_fe
		);
	
	modport slave (
			input	ir, dsr, test_rst, run_idle, capture_dr, shift_dr, update_dr, update_ir,
			input	test_rst_fe, run_idle_fe, capture_dr_fe, shift_dr_fe, update_dr_fe, update_ir_fe
		);
	
endinterface


