/**
 * Module: dsi3_receive_data_collect
 * 
 * gets symbols and build data packets to store
 */
module dsi3_receive_data_collect import dsi3_pkg::*; import project_pkg::*;(
		clk_reset_if.slave  clk_rst,			// clock / reset interface
		input	logic		i_symbol_ready,
		input	logic[3:0]	i_symbol,
		input	logic		i_response_finished,
		input	logic		i_receiving_started_tick,
		input	logic		i_enable_receiver,
		input	logic		i_receive_time_out,
		input	logic		i_rec_pending,
		
		output	logic		o_stop_receiving,
		output	logic		o_received_data,
		output	logic		o_response_finished,
		output	data_ecc_t  o_data,
		output	logic[8:0]	o_symbol_count,
		output	logic		o_symbol_count_overflow
	);

	typedef logic[8:0]	symbol_count_t;
	symbol_count_t		symbol_count_temp, symbol_count_temp_next; 
	data_ecc_t			rec_data_temp, rec_data_temp_next;
	logic				symbol_count_overflow;
	
	logic				response_finished_next, received_data_next;
	logic				save_data;
	
	logic				data_word_ready;
	logic				response_finished_with_unsaved_data;
	
	/*###   data generattion   ######################################################*/
	always_comb begin
		rec_data_temp_next.data = rec_data_temp.data;
		case (symbol_count_temp[1:0])
			2'd0:	rec_data_temp_next.data = {i_symbol, 12'h000};	// clear word on beginning
			2'd1:	rec_data_temp_next.data[11: 8] = i_symbol;
			2'd2:	rec_data_temp_next.data[ 7: 4] = i_symbol;
			2'd3:	rec_data_temp_next.data[ 3: 0] = i_symbol;
		endcase
	end
	
	/*###   symbol count   ######################################################*/
	always_comb begin
		symbol_count_temp_next = symbol_count_temp;

		if (i_symbol_ready == 1'b1) begin
			if (symbol_count_temp != '1) begin
				symbol_count_temp_next = symbol_count_temp + symbol_count_t'(1);
			end
		end

		if (i_receiving_started_tick == 1'b1) begin
			symbol_count_temp_next = '0;
		end
		if (i_enable_receiver == 1'b0) begin
			symbol_count_temp_next = '0;
		end
	end

	/*###   symbol count overflow   ######################################################*/
	always_comb begin
		symbol_count_overflow = (symbol_count_temp_next > symbol_count_t'(255)) ? 1'b1 : 1'b0;
	end
	
	/*###   FFs   ######################################################*/
	always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			symbol_count_temp	<= '0;
			rec_data_temp.data	<= 16'h0000;
			rec_data_temp.ecc	<= ECC_FOR_DATA_0;
			
			o_data.data			<= '0;
			o_data.ecc			<= ECC_FOR_DATA_0;
			o_symbol_count		<= '0;
			o_symbol_count_overflow <= 1'b0;
			o_response_finished <= 1'b0;
			o_received_data		<= 1'b0;
		end
		else begin
			if (i_symbol_ready == 1'b1) begin
				rec_data_temp	<= rec_data_temp_next;
			end
			symbol_count_temp	<= symbol_count_temp_next;
			
			
			if (data_word_ready == 1'b1) begin // data is ready thus store all data from next values (not yet stored in local temporary variables 
				o_symbol_count_overflow <= symbol_count_overflow;
				o_symbol_count <= symbol_count_temp_next;
				o_data		<= rec_data_temp_next;
			end
			else begin
				if (response_finished_with_unsaved_data == 1'b1) begin
					o_symbol_count_overflow <= symbol_count_overflow;
					o_symbol_count <= symbol_count_temp;
					o_data <= rec_data_temp;
				end
			end
			
			o_response_finished <= response_finished_next;
			o_received_data <= received_data_next;
		end
	end
	
	/*###   data word generation   ######################################################*/
	/*
	 * i_symbol_ready -> save data when symbol_count_temp[1:0]==2'b11 (4 symbols received -> new data) => data_word_ready
	 * 
	 * */
	assign	data_word_ready = ((i_symbol_ready == 1'b1) && (symbol_count_temp[1:0] == 2'd3)) ? 1'b1 : 1'b0;
	assign	save_data = data_word_ready | response_finished_with_unsaved_data;
	
	always_comb begin
		if (symbol_count_temp_next <= symbol_count_t'(256)) begin
			if (symbol_count_temp_next >= symbol_count_t'(4))
				received_data_next = save_data;
			else
				received_data_next = 1'b0;
		end
		else
			received_data_next = 1'b0;
	end
	
	always_comb begin
		response_finished_next = 1'b0;
		response_finished_with_unsaved_data = 1'b0;
		o_stop_receiving = 1'b0;

		if (i_response_finished == 1'b1) begin
			if (symbol_count_temp[8:2] != '0) begin
				response_finished_next = 1'b1;
				if (symbol_count_temp[1:0] != 2'd0) begin
					response_finished_with_unsaved_data = 1'b1;				
				end
			end
			o_stop_receiving = 1'b1;
		end
		if (i_receive_time_out == 1'b1) begin
			if (i_rec_pending == 1'b1) begin
				if ((symbol_count_temp[8:2] != '0) || ((symbol_count_temp[8:2] == '0) && (symbol_count_temp_next >= symbol_count_t'(4)) && (data_word_ready == 1'b1))) begin
					response_finished_next = 1'b1;
					if (symbol_count_temp[1:0] != 2'd0) begin
						response_finished_with_unsaved_data = 1'b1;				
					end
				end
				o_stop_receiving = 1'b1;
			end
		end
	end
	
	/*###   ECC_ENCODER   ######################################################*/
	ecc_encoder #(
			.DATA_WIDTH (DATA_WIDTH),
			.ECC_WIDTH  (ECC_WIDTH)
		) i_ecc_enc_dsi (
			.i_data     (rec_data_temp_next.data),
			.o_ecc      (rec_data_temp_next.ecc)
		);

endmodule


