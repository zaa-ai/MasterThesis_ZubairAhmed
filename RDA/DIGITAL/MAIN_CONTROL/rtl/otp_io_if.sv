/**
 * Interface: otp_io
 * 
 * interface containing all I/O signals to analog part of OTP block
 */
interface otp_io_if;
	logic	a_ehv;
	// @SuppressProblem -type fully_non_driven_static_variable -count 5 -length 6
	logic	a_vbg;
	logic	a_vref;
	logic	a_vrr;
	logic	a_vpp;
	// @SuppressProblem -type fully_unread_static_variable -count 1 -length 1
	logic	ehv;
	logic	otp_ready;
	
	modport	master(
			output	ehv, otp_ready,
			input	a_ehv,
			output	a_vbg, a_vref, a_vrr, a_vpp
		);

endinterface


