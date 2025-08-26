`ifndef BIST_PKG
	`define BIST_PKG

	package bist_pkg;

		typedef enum logic [1:0] {
			BIST_INIT = 2'd0,
			BIST_PASS = 2'd1,
			BIST_FAIL = 2'd2,
			BIST_BUSY = 2'd3
		} bist_status_t;

	endpackage
`endif
