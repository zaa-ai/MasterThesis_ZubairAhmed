/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : tdma_buffer_ecc_check.sv
 * Author        : jvoi
 * Creation date : 2023-06-23
 * Description   :
 *------------------------------------------------------------------------------*/
module tdma_header_ecc_check import tdma_pkg::*; #() (
        input   tdma_header_ecc_t   i_header,
        output  tdma_header_t       o_header,
        ecc_error_if.master         ecc_error
    );
    
    import project_pkg::*;
    
    /*###   ECC decoder header   ######################################################*/
    logic   ecc_error_single_header_packet_count, ecc_error_double_header_packet_count;
    ecc_decoder #(.DATA_WIDTH(DATA_WIDTH), .ECC_WIDTH(ECC_WIDTH)) i_ecc_decoder_header_packet_count (
        .i_correct_n(1'b0),
        .i_data     ({i_header.packet_count.unused, i_header.packet_count.packet_count}),
        .i_ecc      (i_header.packet_count.ecc ),
        .o_data     (o_header.packet_count     ),
        .o_ecc_cor  (ecc_error_single_header_packet_count  ),
        .o_ecc_err  (ecc_error_double_header_packet_count  )
    );
    
    logic   ecc_error_single_header_period, ecc_error_double_header_period;
    ecc_decoder #(.DATA_WIDTH(DATA_WIDTH), .ECC_WIDTH(ECC_WIDTH)) i_ecc_decoder_header_period (
        .i_correct_n(1'b0),
        .i_data     (i_header.period.data),
        .i_ecc      (i_header.period.ecc ),
        .o_data     (o_header.period     ),
        .o_ecc_cor  (ecc_error_single_header_period  ),
        .o_ecc_err  (ecc_error_double_header_period  )
    );
    
    assign  ecc_error.single_error = ecc_error_single_header_packet_count | ecc_error_single_header_period;
    assign  ecc_error.double_error = ecc_error_double_header_packet_count | ecc_error_double_header_period;
    
endmodule