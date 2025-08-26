/**
 * Module: spi_core
 *
 * Core module for each SPI
 */
module spi_core import project_pkg::*; import spi_implementation_pkg::*; (
		spi_int_if.slave 		spi_i,
		clk_reset_if.slave      clk_rst,
		input   logic           i_tx_data_available_synced, // stream data_in on sdo (1) or reflect sdi in next word (0)
		input	data_ecc_t      i_tx_data,					// data to send to sdo
		input	data_t          i_status_word,
		input	logic			i_command_running,
        input   logic           i_expect_command_nibble,
        input   spi_command_e   i_command_nibble,
		
		output	logic 			o_txd_en_clear,				// (@posedge sck) clear txd_en flag	| toggling signal
		output	data_ecc_t      o_data_received,			// data received from sdi
		output	logic 			o_rxd_valid,				// toggling signal
        output  logic           o_reset_received,           // toggling signal
        output  logic           o_alignment_error,

        ecc_error_if.master		ecc_error
	);
	
    typedef enum logic {NO_COMMAND, WAS_CRC_COMMAND} previous_command_t;
    previous_command_t   previous_command, previous_command_next;
	
	/* data shift registers */
	shift_register_t		shift_in, shift_in_nxt;
	shift_register_t		shift_out, shift_out_next, shift_out_corrected;
    ecc_t                   shift_out_ecc, shift_out_ecc_next;

	/* counter */
	shift_register_counter_t 	cnt, cnt_nxt, cnt_rst_domain;

	/* hand shake signals */
	logic 	rxd_valid_nxt;
	logic 	txd_en_clear_nxt;

	data_t	crc_out, crc_out_next;
	data_t	crc_out_for_miso, crc_out_for_miso_next;
    
    logic       aligment_error_next;
    logic[1:0]  reset_command_counter, reset_command_counter_next;
    logic       reset_received_next;
    
	/*###   ECC shift out register   ######################################################*/
    ecc_error_if ecc_error_shift_out ();
    logic        ecc_error_shift_out_single_error, ecc_error_shift_out_double_error;
    logic        disable_ecc_detection_shift_out, disable_ecc_detection_shift_out_next;
    
	ecc_encoder #(
			.DATA_WIDTH (DATA_WIDTH),
			.ECC_WIDTH  (ECC_WIDTH)
		) i_ecc_enc_spi_shift_out (
			.i_data     (shift_out_next),
			.o_ecc      (shift_out_ecc_next));
    
    ecc_decoder #(
            .DATA_WIDTH  (DATA_WIDTH),
            .ECC_WIDTH   (ECC_WIDTH)
        ) i_ecc_dec_spi_shift_out (
            .i_correct_n (1'b0),
            .i_data      (shift_out),
            .i_ecc       (shift_out_ecc),
            .o_data      (shift_out_corrected),
            .o_ecc_cor   (ecc_error_shift_out_single_error),
            .o_ecc_err   (ecc_error_shift_out_double_error)
        );
    
    logic ecc_error_shift_out_single_error_prev, ecc_error_shift_out_double_error_prev;
    logic ecc_error_shift_out_single_error_posedge, ecc_error_shift_out_double_error_posedge;
    
    
    logic [2:0] ecc_error_shift_out_single_error_sync, ecc_error_shift_out_double_error_sync;
    
    always_ff@(posedge spi_i.sck or negedge clk_rst.rstn) begin
        if (clk_rst.rstn == 1'b0) begin
            ecc_error_shift_out_single_error_prev <= '0;
            ecc_error_shift_out_double_error_prev <= '0;
            ecc_error_shift_out_single_error_posedge <= '0;
            ecc_error_shift_out_double_error_posedge <= '0;
        end
        else begin
            ecc_error_shift_out_single_error_prev <= ecc_error_shift_out_single_error & ~disable_ecc_detection_shift_out;
            if ((ecc_error_shift_out_single_error & ~disable_ecc_detection_shift_out & (~ecc_error_shift_out_single_error_prev)) == 1'b1)
                ecc_error_shift_out_single_error_posedge <= ~ecc_error_shift_out_single_error_posedge;
            
            ecc_error_shift_out_double_error_prev <= ecc_error_shift_out_double_error & ~disable_ecc_detection_shift_out;
            if ((ecc_error_shift_out_double_error & ~disable_ecc_detection_shift_out & (~ecc_error_shift_out_double_error_prev)) == 1'b1)
                ecc_error_shift_out_double_error_posedge <= ~ecc_error_shift_out_double_error_posedge;
        end    
    end
    
    always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
        if (clk_rst.rstn == 1'b0) begin
            ecc_error_shift_out_single_error_sync <= '0;
            ecc_error_shift_out_double_error_sync <= '0;
        end
        else begin
            ecc_error_shift_out_single_error_sync <= {ecc_error_shift_out_single_error_sync[1:0] , ecc_error_shift_out_single_error_posedge};
            ecc_error_shift_out_double_error_sync <= {ecc_error_shift_out_double_error_sync[1:0] , ecc_error_shift_out_double_error_posedge};
        end
    end
    
    assign  ecc_error_shift_out.single_error = ecc_error_shift_out_single_error_sync[2] ^ ecc_error_shift_out_single_error_sync[1];
    assign  ecc_error_shift_out.double_error = ecc_error_shift_out_double_error_sync[2] ^ ecc_error_shift_out_double_error_sync[1];
    
	/*###   ECC_ENCODER Rx data   ######################################################*/
	logic[DATA_WIDTH-1:0] data_received;
	ecc_t data_received_ecc;

	assign o_data_received.data = data_received;
	assign o_data_received.ecc  = data_received_ecc;

    //ECC has be calculated on received data instead of SDI+shift reg. Otherwise, it may lead to different sampled SDI values
	ecc_encoder #(
			.DATA_WIDTH (DATA_WIDTH),
			.ECC_WIDTH  (ECC_WIDTH)
		) i_ecc_enc_spi (
			.i_data     (data_received),
			.o_ecc      (data_received_ecc)
		);
    
	/*###   ECC_DECODER TX data   ######################################################*/
	logic[DATA_WIDTH-1:0] tx_data_ecc_corrected;
    ecc_error_if    ecc_error_tx_data(), ecc_error_tx_data_edge ();

	ecc_decoder #(
			.DATA_WIDTH  (DATA_WIDTH),
			.ECC_WIDTH   (ECC_WIDTH)
		) i_ecc_dec_spi (
			.i_correct_n (1'b0),
			.i_data      (i_tx_data.data),
			.i_ecc       (i_tx_data.ecc),
			.o_data      (tx_data_ecc_corrected),
			.o_ecc_cor   (ecc_error_tx_data.single_error),
			.o_ecc_err   (ecc_error_tx_data.double_error)
		);
	
	ecc_edge_detection i_ecc_edge_detection (
		.clk_rst    (clk_rst),
		.ecc_in     (ecc_error_tx_data.slave  ),
		.ecc_out    (ecc_error_tx_data_edge.master        )
	);
	
	/*###   NEGEDGE SCK      CLK RESET   ######################################################*/
	always_ff @(negedge spi_i.sck or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin 			// CSB = 1
			crc_out <= CRC_RESET;
			crc_out_for_miso <= CRC_RESET;
			shift_in	<= '0;
			o_rxd_valid	<= 1'b0;
			data_received <= '0;
            o_reset_received <= '0;
		end
		else begin
			crc_out <= crc_out_next;
			crc_out_for_miso <= crc_out_for_miso_next;
			shift_in		<= shift_in_nxt;
			o_rxd_valid 	<= rxd_valid_nxt;
			if (cnt == '0) begin
				data_received <= shift_in_nxt;
                o_reset_received <= reset_received_next;
			end
		end
	end
	
	assign shift_in_nxt 	= {shift_in[shift_length-2:0], spi_i.sdi};

	/*###   POSEDGE SCK      CLK RESET   ######################################################*/
	always_ff @(posedge spi_i.sck or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
			cnt_rst_domain	<= '0;
			o_txd_en_clear	<= 1'b0;
            previous_command <= NO_COMMAND;
            reset_command_counter <= '0;
            shift_out <= '1;
            shift_out_ecc <= ECC_FOR_DATA_FFFF;
            disable_ecc_detection_shift_out <= 1'b0;
		end
		else begin
			cnt_rst_domain	<= cnt_nxt;
			o_txd_en_clear	<= txd_en_clear_nxt;
            previous_command	<= previous_command_next;
            shift_out <= shift_out_next;
            shift_out_ecc <= shift_out_ecc_next;
            disable_ecc_detection_shift_out <= disable_ecc_detection_shift_out_next;
            if (cnt == '0) begin
                reset_command_counter <= reset_command_counter_next;
            end
		end
	end
	
	/*###   POSEDGE SCK      CSB RESET   ######################################################*/
	always_ff @(posedge spi_i.sck or negedge spi_i.csb_resn) begin
		if (spi_i.csb_resn == 1'b0)  begin 			// CSB = 1
			cnt				<= '0;
		end
		else begin
			cnt				<= cnt_nxt;
		end
    end
    
	/*###   POSEDGE CSB      CLK RESET   ######################################################*/
	always_ff @(posedge spi_i.csb or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0)  begin
            o_alignment_error     <= '0;
		end
		else begin
            o_alignment_error	  <= aligment_error_next;
		end
    end
    
	/*#########################################################################################*/
    logic   after_reset_command;
    always_comb begin
		// default: shift out and reflect the input stream for next word
		shift_out_next = {shift_out_corrected[shift_length-2:0], shift_in[0]};
		txd_en_clear_nxt = o_txd_en_clear;
        previous_command_next = previous_command;
        disable_ecc_detection_shift_out_next = 1'b0;
        
		if (cnt == '0) begin
            case(previous_command)
                WAS_CRC_COMMAND: begin
    				shift_out_next = i_status_word;
                    previous_command_next = NO_COMMAND;
                end
                NO_COMMAND : begin
                    // if read access then overwrite the reflected word with data_in
                    if (i_tx_data_available_synced == 1'b1) begin
                        shift_out_next = tx_data_ecc_corrected;
                        txd_en_clear_nxt = ~o_txd_en_clear;
                    end
                    if ((i_command_running == 1'b0) || ((i_expect_command_nibble == 1'b1) && (i_command_nibble != spi_command_e'(shift_in[15:12]))) )begin
                        if ((spi_command_e'(shift_in[15:12]) == CRC_OUT)) begin
                            shift_out_next = crc_out_for_miso;
                            previous_command_next = WAS_CRC_COMMAND;
                        end
                        if ((spi_command_e'(shift_in[15:12]) == IC_STATUS)) begin
                            shift_out_next = i_status_word;
                            disable_ecc_detection_shift_out_next = 1'b1;
                        end
                    end
                end
            endcase
        end
        if (after_reset_command == 1'b1) begin
            shift_out_next = i_status_word;
            previous_command_next = NO_COMMAND;
        end
    end
    
    // QUICKFIX for P52144-215:
    always_comb begin
        rxd_valid_nxt   = o_rxd_valid;      
        if (cnt == '0) begin
            if (reset_command_counter == '1) begin
                if (shift_in[14:0] == SPI_RESET_COMMAND_WORD[14:0]) begin
                end else begin
                    rxd_valid_nxt   = ~o_rxd_valid;
                end
            end
            else begin
                rxd_valid_nxt   = ~o_rxd_valid;
            end
        end
    end
    
    always_comb begin
        reset_command_counter_next = reset_command_counter;
        reset_received_next = o_reset_received;
        after_reset_command = 1'b0;
        if (cnt == '0) begin
            if (reset_command_counter == '1) begin
                if (shift_in[14:0] == SPI_RESET_COMMAND_WORD[14:0]) begin
                    reset_received_next = ~o_reset_received;
                end
                if (shift_in[15:1] == SPI_RESET_COMMAND_WORD[15:1]) begin
                    after_reset_command = 1'b1;
                end
            end
            if (data_received == SPI_RESET_COMMAND_WORD) begin
                reset_command_counter_next = reset_command_counter + 2'd1;
            end
            else begin
                reset_command_counter_next = '0;
            end
        end
    end
    
	always_comb begin
		cnt_nxt = cnt + shift_register_counter_t'(1);			// increment (count)
		if (cnt >= shift_register_counter_t'(shift_length - 1)) begin
			cnt_nxt = '0;					// reset counter to 0
		end
	end

	/* output assignments */
	assign spi_i.sdo 		= shift_out_corrected[shift_length-1];
    
    always_comb begin
        if (cnt_rst_domain == shift_length_width'(0)) aligment_error_next = o_alignment_error;
        else aligment_error_next = ~o_alignment_error;
    end

	/*###   CRC   ######################################################*/
	/*###   CRC calculation   ######################################################*/
	always_comb begin
		if ((cnt == '0) && ((previous_command == WAS_CRC_COMMAND) || (after_reset_command == 1'b1))) begin
			crc_out_next = CRC_RESET;
		end
		else begin
			crc_out_next[0] = shift_out_corrected[shift_length-1] ^ crc_out[15];
			crc_out_next[4:1] = crc_out[3:0];
			crc_out_next[5] = crc_out[4] ^ crc_out[15];
			crc_out_next[11:6] = crc_out[10:5];
			crc_out_next[12] = crc_out[11] ^ crc_out[15];
			crc_out_next[15:13] = crc_out[14:12];
        end
	end
	
	always_comb begin
		crc_out_for_miso_next = crc_ccitt_16_word(crc_out_next, 16'h0000); // 0x0000 has to be appended to get the last CRC for the last word to be correct
	end
	
    assign  ecc_error.single_error = ecc_error_tx_data_edge.single_error | ecc_error_shift_out.single_error;
    assign  ecc_error.double_error = ecc_error_tx_data_edge.double_error | ecc_error_shift_out.double_error;
    
endmodule
