/**
 * Module: spi_tx_fifo
 *
 * SPI FIFO for outputing data at SPI
 */
module spi_tx_fifo import project_pkg::*; #(
		parameter data_ecc_t reset_value = {16'hffff, 6'h3f}
	)(
		clk_reset_if.slave clk_rst,

		input	data_ecc_t	i_fifo_data,
		input	logic	i_set_fifo_data,

		input	logic	i_pop_data,
		input	logic	i_reset,
		output	logic	o_data_available_for_core,
        output  logic   o_some_data_in_fifo,
		output	logic	o_full,

		output	data_ecc_t	o_data
	);

		/*###   TX Data FIFO   ######################################################*/
	data_ecc_t tx_fifo[1:0], tx_fifo_nxt[1:0];
	logic [1:0]  txd_request, txd_request_nxt;
	logic shift_fifo;

	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			txd_request <= 2'b0;
			tx_fifo		<= '{reset_value, reset_value};
		end
		else begin
			txd_request <= txd_request_nxt;
			tx_fifo		<= tx_fifo_nxt;
		end
	end

	logic fifo_first_word_out_second_in;
	assign	fifo_first_word_out_second_in = ((txd_request[0] == 1'b0) && (txd_request[1] == 1'b1)) ? 1'b1 : 1'b0;

	always_comb begin
		shift_fifo = 1'b0;
		if ((fifo_first_word_out_second_in == 1'b1) || (i_pop_data == 1'b1))
			shift_fifo = 1'b1;
	end

	always_comb begin
		txd_request_nxt = txd_request;
		tx_fifo_nxt		= tx_fifo;

		if (i_reset == 1'b1) begin
			txd_request_nxt = 2'b00;
		end
		else begin
			if (shift_fifo == 1'b1 ) begin
				txd_request_nxt[0]	= txd_request[1];
				txd_request_nxt[1]	= 1'b0;
				tx_fifo_nxt			= '{reset_value, tx_fifo[1]};
			end
			if (i_set_fifo_data == 1'b1) begin
				if (i_reset == 1'b0) begin
					txd_request_nxt[1] = 1'b1;
				end
				tx_fifo_nxt[1] = i_fifo_data;
			end
		end
	end

	assign	o_data_available_for_core = txd_request[0];
    assign  o_some_data_in_fifo = |(txd_request);
	assign	o_data = tx_fifo[0];
	assign	o_full = (txd_request==2'b11) ? 1'b1 : 1'b0;


	`ifdef VCS
		property fifo_set_while_full;
			i_set_fifo_data |-> ~o_full;
		endproperty
		property pop_not_twice;
			i_pop_data |=> ~i_pop_data;
		endproperty
		//TODO: time consuming
		as_pop_not_twice : assert property (@(posedge clk_rst.clk) pop_not_twice) else $error("pop_not_twice: data of FIFO was poped twice in a row!");
		cov_pop_not_twice : cover property (@(posedge clk_rst.clk) pop_not_twice);
		as_fifo_set_while_full : assert property (@(posedge clk_rst.clk) fifo_set_while_full) else $error("fifo_set_while_full: SPI TX fifo set while FIFO is full");
		cov_fifo_set_while_full : cover property (@(posedge clk_rst.clk) fifo_set_while_full);
		`endif

endmodule


