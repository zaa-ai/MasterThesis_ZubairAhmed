/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : spi_tdma_reader.sv
 * Author        : jvoi
 * Creation date : 2023-04-03
 * Description   : module for reading TDMA scheme information for the SPI
 *                  - read only packet count and word count information of selected channel
 *------------------------------------------------------------------------------*/
module spi_tdma_reader import spi_implementation_pkg::*; (
        clk_reset_if.slave          clk_rst,
        elip_full_if.master         elip,
        spi_tdma_reader_if.slave    tdma_reader,
        input      logic            current_channel
);
    import project_pkg::*;
    
    always_comb begin
        elip.rd = 1'b0;
        elip.addr = BASE_ADDR_DSI_TDMA[current_channel];
        tdma_reader.ready = 1'b0;
        tdma_reader.data = elip.data_read;
        case(tdma_reader.action)
            READ_FRAME_INFO : begin
                elip.rd = 1'b1;
                tdma_reader.ready = elip.ready;
                
            end
            READ_PACKET_INFO : begin
                elip.rd = 1'b1;
                elip.addr = BASE_ADDR_DSI_TDMA[current_channel]+ELIP_ADDR_WIDTH'(4)+(tdma_reader.index*3);
                tdma_reader.ready = elip.ready;
            end
            default: begin
            end
        endcase
    end
    
    assign  elip.data_write.data = '0;
    assign  elip.data_write.ecc = ECC_FOR_DATA_0;
    assign  elip.wr = 1'b0;
    
endmodule