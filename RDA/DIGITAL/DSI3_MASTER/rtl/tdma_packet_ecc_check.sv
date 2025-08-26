/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : tdma_buffer_ecc_check.sv
 * Author        : jvoi
 * Creation date : 2023-06-23
 * Description   :
 *------------------------------------------------------------------------------*/
module tdma_packet_ecc_check import tdma_pkg::*; #() (
        input   tdma_packet_ecc_t   i_packet,
        output  tdma_packet_t       o_packet,
        ecc_error_if.master         ecc_error
    );
    
    import project_pkg::*;
    
    logic   ecc_error_single_packet_earliest, ecc_error_double_packet_earliest;
    logic   ecc_error_single_packet_latest, ecc_error_double_packet_latest;
    logic   ecc_error_single_packet_info, ecc_error_double_packet_info;
    
    ecc_decoder #(.DATA_WIDTH(DATA_WIDTH), .ECC_WIDTH(ECC_WIDTH)) i_ecc_decoder_packet_earliest (
        .i_correct_n(1'b0),
        .i_data     (i_packet.earliest.data),
        .i_ecc      (i_packet.earliest.ecc ),
        .o_data     (o_packet.earliest     ),
        .o_ecc_cor  (ecc_error_single_packet_earliest  ),
        .o_ecc_err  (ecc_error_double_packet_earliest  )
    );
    
    ecc_decoder #(.DATA_WIDTH(DATA_WIDTH), .ECC_WIDTH(ECC_WIDTH)) i_ecc_decoder_packet_latest (
        .i_correct_n(1'b0),
        .i_data     (i_packet.latest.data),
        .i_ecc      (i_packet.latest.ecc ),
        .o_data     (o_packet.latest     ),
        .o_ecc_cor  (ecc_error_single_packet_latest  ),
        .o_ecc_err  (ecc_error_double_packet_latest  )
    );
    
    ecc_decoder #(.DATA_WIDTH(DATA_WIDTH), .ECC_WIDTH(ECC_WIDTH)) i_ecc_decoder_packet_info (
        .i_correct_n(1'b0),
        .i_data     (i_packet.info.data),
        .i_ecc      (i_packet.info.ecc ),
        .o_data     (o_packet.info     ),
        .o_ecc_cor  (ecc_error_single_packet_info  ),
        .o_ecc_err  (ecc_error_double_packet_info  )
    );
    
    assign  ecc_error.single_error = ecc_error_single_packet_earliest | ecc_error_single_packet_latest | ecc_error_single_packet_info;
    assign  ecc_error.double_error = ecc_error_double_packet_earliest | ecc_error_double_packet_latest | ecc_error_double_packet_info;
    
endmodule