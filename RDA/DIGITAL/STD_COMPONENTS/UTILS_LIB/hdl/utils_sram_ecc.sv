
`timescale 1ns/10ps

module utils_sram_ecc #(
		parameter ADDR_WIDTH    = 10,
		parameter PART_WIDTH    = 8,
		parameter PART_ECC_BITS = 5,
		parameter PROTECT_ADDR  = 0
		)(
		input                                       clk,
		input                                       nrst,

		input                                       parity_swap,
		output logic                                parity_event,
		output logic                                corrected_event,
		input                   [PART_ECC_BITS-1:0] ecc_val,
		input                                       ecc_sel,

		input                                       ce,
		input                                       oe,
		input                      [ADDR_WIDTH-1:0] addr,
		input                      [PART_WIDTH-1:0] wdata,
		output                     [PART_WIDTH-1:0] rdata,

		output logic [PART_WIDTH+PART_ECC_BITS-1:0] wdata_sram, // SRAM IP write data
		input        [PART_WIDTH+PART_ECC_BITS-1:0] rdata_sram  // SRAM IP read data
		);

	logic                  rdata_cycle;
	logic [ADDR_WIDTH-1:0] prev_addr;

	// DMOS: due to one cycle access we need rdata_cyce generated combinatorical
	
	assign rdata_cycle = ce & oe;

	localparam EXT_PART_WIDTH = PROTECT_ADDR  ? (ADDR_WIDTH + PART_WIDTH) : PART_WIDTH;

	logic [EXT_PART_WIDTH-1:0] wdata_bus;
	logic [EXT_PART_WIDTH-1:0] rdata_bus;

	always_comb
	begin
		wdata_bus = PROTECT_ADDR  ? {addr, wdata} : wdata;
	end

	logic [EXT_PART_WIDTH+PART_ECC_BITS-1:0] wdata_mem;
	logic [EXT_PART_WIDTH+PART_ECC_BITS-1:0] rdata_mem;

	wire detected, corrected;

	generate
		if (PART_ECC_BITS == 5) begin : part_ecc_bit_5

			ecc_5_hd4_shell #(
					.DATA_WIDTH (PART_WIDTH),
					.ADDR_WIDTH (PROTECT_ADDR ? ADDR_WIDTH : 0),
					.SERIAL     (0)
				) ecc_5_hd4_shell_inst(
					.wdata_bus (wdata_bus),
					.wdata_mem (wdata_mem),
					.rdata_mem (rdata_mem),
					.rdata_bus (rdata_bus),
					.i_disable (1'b0),
					.corrected (corrected),
					.detected  (detected)
				);

		end
		else if (PART_ECC_BITS == 6) begin : part_ecc_bit_6

			ecc_6_hd4_shell #(
					.DATA_WIDTH (PART_WIDTH),
					.ADDR_WIDTH (PROTECT_ADDR ? ADDR_WIDTH : 0),
					.SERIAL     (0)
				) ecc_6_hd4_shell_inst(
					.wdata_bus (wdata_bus),
					.wdata_mem (wdata_mem),
					.rdata_mem (rdata_mem),
					.rdata_bus (rdata_bus),
					.i_disable (1'b0),
					.corrected (corrected),
					.detected  (detected)
				);

		end
		else if (PART_ECC_BITS == 7) begin : part_ecc_bit_7

			ecc_7_hd4_shell #(
					.DATA_WIDTH (PART_WIDTH),
					.ADDR_WIDTH (PROTECT_ADDR ? ADDR_WIDTH : 0),
					.SERIAL     (0)
				) ecc_7_hd4_shell_inst(
					.wdata_bus (wdata_bus),
					.wdata_mem (wdata_mem),
					.rdata_mem (rdata_mem),
					.rdata_bus (rdata_bus),
					.i_disable (1'b0),
					.corrected (corrected),
					.detected  (detected)
				);

		end
	endgenerate


	always @(negedge nrst or posedge clk)
	begin
		if (!nrst) begin
			parity_event <= 1'b0;
			corrected_event <= 1'b0;
		end
		else begin
			parity_event <= 1'b0;
			corrected_event <= 1'b0;

			if (rdata_cycle) begin
				if (detected) begin
					parity_event <= 1'b1;
				end
				if (corrected) begin
					corrected_event <= 1'b1;
				end

			end
		end
	end

	always_comb
	begin
		wdata_sram[         0 +:    PART_WIDTH] = wdata_mem[             0 +:    PART_WIDTH];  // data bits
		wdata_sram[PART_WIDTH +: PART_ECC_BITS] = wdata_mem[EXT_PART_WIDTH +: PART_ECC_BITS];  // ECC bits

		if (parity_swap) begin
			// swap data LSBs and ECC bits
			wdata_sram[         0 +: PART_ECC_BITS] = wdata_mem[EXT_PART_WIDTH +: PART_ECC_BITS];
			wdata_sram[PART_WIDTH +: PART_ECC_BITS] = wdata_mem[             0 +: PART_ECC_BITS];
		end

		if (ecc_sel) begin
			wdata_sram[PART_WIDTH +: PART_ECC_BITS] = ecc_val;
		end
	end

	always_comb
	begin
		rdata_mem[0 +: EXT_PART_WIDTH] = { (ADDR_WIDTH)'(0), rdata_sram[PART_WIDTH-1:0]};                           // data bits
		if (PROTECT_ADDR) begin
			rdata_mem[0 +: EXT_PART_WIDTH] = {addr, rdata_sram[PART_WIDTH-1:0]};            // addr and data bits
		end
		rdata_mem[EXT_PART_WIDTH +: PART_ECC_BITS] = rdata_sram[PART_WIDTH +: PART_ECC_BITS];  // ECC bits

		if (parity_swap) begin
			// swap data LSBs and ECC bits
			rdata_mem[EXT_PART_WIDTH +: PART_ECC_BITS] = rdata_sram[         0 +: PART_ECC_BITS];
			rdata_mem[             0 +: PART_ECC_BITS] = rdata_sram[PART_WIDTH +: PART_ECC_BITS];
		end
	end

	assign rdata = rdata_bus[PART_WIDTH-1:0];

	`ifdef SVA
		//=========================================================================
		// SV assertions
		//=========================================================================

		// VCS coverage off
		reg time_zero;

		initial begin
			time_zero = 1'b1;
			#1;
			time_zero = 1'b0;
		end
		// VCS coverage on

		clocking cb @(posedge clk);

			property param_check_ecc_bits_5_p;
				(EXT_PART_WIDTH <= 10) |-> (PART_ECC_BITS == 5);
			endproperty

			property param_check_ecc_bits_6_p;
				(EXT_PART_WIDTH > 10) && (EXT_PART_WIDTH <= 25) |-> (PART_ECC_BITS == 6);
			endproperty

			property param_check_ecc_bits_7_p;
				(EXT_PART_WIDTH > 25) |-> (PART_ECC_BITS == 7);
			endproperty

			property param_check_max_ext_part_width_p;
				(EXT_PART_WIDTH < 56);
			endproperty

			property parity_swap_never_x_p;
				disable iff (time_zero) !$isunknown(parity_swap);
			endproperty

			property ecc_val_never_x_p;
				disable iff (time_zero) !$isunknown(ecc_val);
			endproperty

			property ecc_sel_never_x_p;
				disable iff (time_zero) !$isunknown(ecc_sel);
			endproperty

		endclocking

		param_check_ecc_bits_5         : assert property (cb.param_check_ecc_bits_5_p        ) else $fatal;
		param_check_ecc_bits_6         : assert property (cb.param_check_ecc_bits_6_p        ) else $fatal;
		param_check_ecc_bits_7         : assert property (cb.param_check_ecc_bits_7_p        ) else $fatal;
		param_check_max_ext_part_width : assert property (cb.param_check_max_ext_part_width_p) else $fatal;
		parity_swap_never_x            : assert property (cb.parity_swap_never_x_p           ) else $fatal;
		ecc_val_never_x                : assert property (cb.ecc_val_never_x_p               ) else $fatal;
		ecc_sel_never_x                : assert property (cb.ecc_sel_never_x_p               ) else $fatal;

			`endif

endmodule

