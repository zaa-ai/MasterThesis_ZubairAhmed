`ifndef _CRC_CALCULATION_PKG
`define _CRC_CALCULATION_PKG

package crc_calculation_pkg;
	
	import common_pkg::*;
	import dsi3_pkg::*;
		
	localparam logic[15:0] crc_ccitt_16_polynom = 16'b0001_0000_0010_0001;
	
	localparam logic[15:0] spi_crc_seed_16bit = 16'h84cf;
	localparam logic[15:0] dsi3_crc_seed_16bit = 16'hffff;
	
	/**
	 * Function crc_ccitt_16
	 * 
	 * Calculates the CRC CCITT 16 from a queue of logic[15:0] (data)
	 * data_msb_first: if set to 1, the calculation starts from the highest word in the queue (=data[data.size()-1])
	 */
	function logic[15:0] spi_crc_ccitt_16 (logic[15:0] data[$], logic[15:0] crc_seed = spi_crc_seed_16bit, bit data_msb_first = 1'b1);
		logic[15:0] crc;
		crc = crc_seed;
		if (data_msb_first) begin
			for (int i=0; i<data.size(); i++)
				crc = spi_crc_ccitt_16_word(crc, data[i]);
		end else begin
			for (int i=(data.size()-1); i>=0; i--)
				crc = spi_crc_ccitt_16_word(crc, data[i]);				
		end
		return crc;
	endfunction
	
	function logic[15:0] spi_crc_ccitt_16_word(input logic[15:0] crc, input logic[15:0] data);
		for (int k=15; k>=0; k--) begin
			crc = {crc[14:0], data[k]} ^ ({16{crc[15]}} & crc_ccitt_16_polynom);
		end
		return crc;
	endfunction
	
	function bit spi_ends_with_correct_crc(logic[15:0] queue[$]);
		return spi_crc_ccitt_16(queue) == 16'h0000;
	endfunction
	
	function logic[15:0] spi_calculate_correct_crc(logic[15:0] queue[$], logic[15:0] crc_seed = spi_crc_seed_16bit);
		return spi_calculate_crc(1'b1, queue, crc_seed);
	endfunction
	
	function logic[15:0] spi_calculate_crc(bit crc_correct, logic[15:0] queue[$], logic[15:0] crc_seed = spi_crc_seed_16bit);
		logic[15:0] temp_crc;
		logic[15:0] correct_crc;
		queue.push_back(16'h0000);
		correct_crc  = spi_crc_ccitt_16(queue, crc_seed);
		if (crc_correct) begin
			temp_crc  = correct_crc;
		end
		else begin
			do begin
				temp_crc = shortint'($random());
			end while (temp_crc  == correct_crc );
		end
		return temp_crc;
	endfunction
	
	function logic[7:0] get_dsi3_seed(logic[3:0] data[$], dsi3_pkg::sid_length_e source_id_symbols);
		case (source_id_symbols)
			dsi3_pkg::SID_0Bit: return 8'hff;
			dsi3_pkg::SID_4Bit: return data[0];
			dsi3_pkg::SID_8Bit: return {data[0], data[1]};
			default: return 8'h00;
		endcase
	endfunction
	
	function logic[15:0] dsi3_calculate_correct_crc(logic[3:0] data[$], sid_length_e crc_type);
		return dsi3_calculate_crc(1'b1, data, crc_type);
	endfunction
	
	function logic[15:0] dsi3_calculate_crc(bit crc_correct, logic[3:0] data[$], sid_length_e crc_type);
		logic [15:0] calculated_crc;
		logic[7:0] crc_seed;
		case (crc_type)
			SID_16Bit_CRC : begin
				logic[15:0] words[$];
				if (convert_queue#(4, 16)::convert(data, words, 1)) return 16'd0;
				calculated_crc = spi_calculate_correct_crc(words, dsi3_crc_seed_16bit);
				if (crc_correct == 1'b0) begin
					logic [15:0] temp_crc;
					do begin
						temp_crc = 16'($urandom_range(16'hffff, 0));
					end while (temp_crc == calculated_crc);
					calculated_crc = temp_crc;
				end
			end
			default: begin
				crc_seed = get_dsi3_seed(data, crc_type);
				calculated_crc = {8'd0, dsi3_crc(data, crc_seed)};
				if (crc_correct == 1'b0) begin
					logic [15:0] temp_crc;
					do begin
						temp_crc = 16'($urandom_range(16'hffff, 0));
					end while (temp_crc[7:0] == calculated_crc[7:0]);
					calculated_crc = temp_crc;
				end
			end
		endcase
		return calculated_crc;
	endfunction

	function logic[7:0] dsi3_crc(input logic[3:0] data[$], input logic[7:0] crc_seed = 8'hff);
		logic[7:0] temp;
		temp = crc_seed;
		for (int j=0; j<data.size(); j++) begin
			temp = dsi3_crc_calc(data[j], temp);
		end
		return temp;
	endfunction

	function logic[7:0] dsi3_crc_words(input logic[15:0] data[$], input logic[7:0] crc_seed);
		logic[7:0] temp;
		temp = crc_seed;
		for (int j=0; j<data.size(); j++) begin
			for (int i=4; i>0; i--) begin
				temp = dsi3_crc_calc(data[j][(i*4)-1-:4], temp);
			end
		end
		return temp;
	endfunction

	function logic[7:0] dsi3_crc_calc(input logic [3:0] data, input logic[7:0] crc_in);
		logic[7:0] crc;
		crc  =  crc_in;
		for (int i=3; i>=0; i--) begin	// start with MSBs
			crc = dsi3_crc_calc_bitwise(data[i], crc);
		end
		return crc;
	endfunction

	function logic[7:0] dsi3_crc_calc_bitwise(input logic data, input logic[7:0] crc_in);
		logic[7:0] crc_polynom;
		logic[7:0] crc_bitwise;
		crc_polynom = 8'b00101111;
		crc_bitwise = {crc_in[6:0], data} ^ ({8{crc_in[7]}} & crc_polynom);
		return crc_bitwise;
	endfunction
	
endpackage : crc_calculation_pkg

`endif
