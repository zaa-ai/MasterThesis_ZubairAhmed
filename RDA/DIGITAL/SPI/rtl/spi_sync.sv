/**
 * Module: spi_sync
 * 
 * module for synchronizing SPI signals into system clock domain and vice-versa
 */
module spi_sync import project_pkg::*; (
		clk_reset_if.slave	clk_rst,
		input	logic	i_spi_clk,
		
		// to SPI
		input	logic	i_tx_data_available,
		output	logic	o_tx_data_available_synced,
		input	logic	i_command_in_pending,
		output	logic	o_command_in_pending_synced,
        input   logic   i_expect_command_nibble,
        output  logic   o_expect_command_nibble,
		
		// to core
		input	logic	i_tx_data_taken_over,		// toggling
		output	logic	o_tx_data_taken_over_edge,
		input	logic	i_rxd_valid,				// toggling
		output	logic	o_rxd_valid_edge,
        input   logic   i_alignment_error,          // toggling
        output  logic   o_alignment_error_edge,
        input   logic   i_reset_received,           // toggling
        output  logic   o_reset_received_edge,
        input   data_ecc_t  i_rx_data,
        output  data_ecc_t  o_rx_data
	);
	
	/*###   to SPI   ######################################################*/
	logic[1:0]	tx_data_available;
	logic[1:0]	command_in_pending;
    logic[1:0]  expect_command_nibble;
	always_ff@(posedge i_spi_clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			tx_data_available <= '0;
			command_in_pending <= 2'b0;
            expect_command_nibble <= '0;
		end
		else begin
			tx_data_available <= {tx_data_available[0], i_tx_data_available};
			command_in_pending <= {command_in_pending[0], i_command_in_pending};
            expect_command_nibble <= {expect_command_nibble[0], i_expect_command_nibble};
		end
	end
	assign	o_tx_data_available_synced = tx_data_available[1];
	assign	o_command_in_pending_synced = command_in_pending[1];
    assign  o_expect_command_nibble = expect_command_nibble[1];
	
	/*###   to core   ######################################################*/
	logic [2:0]	tx_data_taken_over;
	logic [3:0] rxd_valid_sync;
    logic [2:0] alignment_error;
    logic [2:0] reset_received;
    logic       store_rx_data;
    
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			tx_data_taken_over  <= '0;
			rxd_valid_sync[0]   <= '0;
			rxd_valid_sync[3:2] <= '0;
            alignment_error     <= '0;
            reset_received      <= '0;
            o_rx_data           <= EMPTY_DATA;
		end
		else begin
			tx_data_taken_over  <= {tx_data_taken_over[1:0], i_tx_data_taken_over};
			rxd_valid_sync[0]   <= i_rxd_valid;
            rxd_valid_sync[3:2] <= {rxd_valid_sync[2], rxd_valid_sync[1]};
            alignment_error     <= {alignment_error[1:0], i_alignment_error};
            reset_received <= {reset_received[1:0], i_reset_received};
            if (store_rx_data == 1'b1)
                o_rx_data <= i_rx_data;
		end
	end
	always_ff@(negedge clk_rst.clk or negedge clk_rst.rstn) begin //FIXME: get correct reset for negedge clock domain!
		if (clk_rst.rstn == 1'b0) begin
			rxd_valid_sync[1] <= '0;
		end
		else begin
            rxd_valid_sync[1] <= rxd_valid_sync[0];
		end
	end
	assign o_tx_data_taken_over_edge = ^(tx_data_taken_over[2:1]);
	assign o_rxd_valid_edge = ^(rxd_valid_sync[3:2]);
    assign store_rx_data = ^(rxd_valid_sync[2:1]);
    assign o_alignment_error_edge = ^(alignment_error[2:1]);
    assign o_reset_received_edge  = ^(reset_received[2:1]);
	
endmodule


