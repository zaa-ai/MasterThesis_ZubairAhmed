/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : elip_demuxer.sv
 * Author        : jvoi
 * Creation date : 2023-04-03
 * Description   :
 *------------------------------------------------------------------------------*/
module elip_demuxer import project_pkg::*; (
        clk_reset_if.slave   clk_rst,
        elip_full_if.slave   elip,
        elip_full_if.master  elip_tdma[DSI_CHANNELS-1:0]
    );
    
    `include "DW_ecc_function.inc"
    
    data_ecc_t  random_data;
    
    generate
        genvar i;
        for (i = 0; i < DSI_CHANNELS; i++) begin : generate_array_assignments
            assign  elip_tdma[i].data_write = '{'0, ECC_FOR_DATA_0};
            assign  elip_tdma[i].wr = 1'b0;
            assign  elip_tdma[i].addr = elip.addr;
            always_comb begin
                if ((elip.addr >= BASE_ADDR_DSI_TDMA[i]) && (elip.addr < BASE_ADDR_DSI_TDMA[i] + SIZE_DSI_TDMA)) begin
                    elip_tdma[i].rd = 1'b1;
                end
                else begin
                    elip_tdma[i].rd = 1'b0; 
                end
            end
        end
    endgenerate
    
    always@(posedge elip.rd) begin
        random_data = get_random_data();
    end
    
    always_comb begin
        elip.ready = 1'b0;
        elip.data_read = '{'0, ECC_FOR_DATA_0};
        if (elip.rd == 1'b1) begin
            if ((elip.addr >= BASE_ADDR_DSI_TDMA[0]) && (elip.addr < BASE_ADDR_DSI_TDMA[0] + SIZE_DSI_TDMA)) begin
                elip.data_read = elip_tdma[0].data_read;
                elip.ready = elip_tdma[0].ready;
            end
            else begin
                if ((elip.addr >= BASE_ADDR_DSI_TDMA[1]) && (elip.addr < BASE_ADDR_DSI_TDMA[1] + SIZE_DSI_TDMA)) begin
                    elip.data_read = elip_tdma[1].data_read;
                    elip.ready = elip_tdma[1].ready;
                end
                else begin
                    elip.data_read = random_data;
                    elip.ready = ~clk_rst.clk;
                end
            end
        end
        
    end
    
    always_comb begin
        if (elip.data_write.data != '0)
            $fatal("spi_elip_read.data_write has been set a value! 0x%4h", elip.data_write);
        if (elip.wr != 1'b0)
            $fatal("spi_elip_read.wr has been set a value! b%1b", elip.wr);
    end
    
    function automatic data_ecc_t get_random_data();
        data_ecc_t  data;
        data.data = $urandom_range('hffff,0);
        // @SuppressProblem -type assign_truncation_non_const_other -count 1 -length 1
        data.ecc = DWF_ecc_gen_chkbits(16,6,data.data);
        return data;
    endfunction
    
endmodule