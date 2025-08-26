/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : tdma_buffer_ecc_check.sv
 * Author        : jvoi
 * Creation date : 2023-06-23
 * Description   :
 *------------------------------------------------------------------------------*/
module tdma_ecc_check import tdma_pkg::*; #() (
        input   tdma_packet_ecc_t   i_packet,
        input   tdma_packet_ecc_t   i_packet_next,
        input   tdma_header_ecc_t   i_header,
        output  tdma_packet_t       o_packet,
        output  tdma_packet_t       o_packet_next,
        output  tdma_header_t       o_header,
        ecc_error_if.master         ecc_error
    );
    
    import project_pkg::*;
    
    ecc_error_if ecc_error_packet();
    ecc_error_if ecc_error_packet_next();
    ecc_error_if ecc_error_header();
    
    tdma_packet_ecc_check i_tdma_packet_ecc_check (
        .i_packet (i_packet ),
        .o_packet (o_packet ),
        .ecc_error(ecc_error_packet.master)
    );
    
    tdma_packet_ecc_check i_tdma_packet_next_ecc_check (
        .i_packet (i_packet_next ),
        .o_packet (o_packet_next ),
        .ecc_error(ecc_error_packet_next.master)
    );
    
    tdma_header_ecc_check i_tdma_header_ecc_check (
        .i_header (i_header ),
        .o_header (o_header ),
        .ecc_error(ecc_error_header.master)
    );
    
    assign  ecc_error.single_error = ecc_error_packet.single_error | ecc_error_packet_next.single_error | ecc_error_header.single_error;
    assign  ecc_error.double_error = ecc_error_packet.double_error | ecc_error_packet_next.double_error | ecc_error_header.double_error;
    
endmodule