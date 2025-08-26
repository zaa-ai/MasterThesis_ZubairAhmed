`ifdef VCS
/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : tdma_scheme_visualizer.sv
 * Author        : jvoi
 * Creation date : 2023-04-19
 * Description   : Module for visualization of TDMA (scheme) information in simulation
 *------------------------------------------------------------------------------*/
module tdma_scheme_visualizer import project_pkg::*; (
        clk_reset_if.slave                  clk_rst,
        input   logic                       i_tick_1us,
        input   data_t                      i_current_time_in_period
    );
    import dsi3_pkg::*;
    import tdma_pkg::*;
    import spi_implementation_pkg::*;
    
    typedef struct {
        sid_length_e  id_config;
        logic[7:0]    symbol_count;
    } tdma_visual_packet_header_t;
    
    typedef struct {
        shortint  earliest;
        shortint  latest;
        tdma_visual_packet_header_t    info;
    } tdma_visual_packet_t;
    
    typedef struct packed {
        shortint  packet_count;
        shortint  period;
    } tdma_visual_header_t;
    
    typedef struct  {
        tdma_visual_header_t    header;
        tdma_visual_packet_t    packets[15];
    } tdma_t;
    
    typedef struct {
        bit start;
        int index;
    } packet_start_t;
    
//    tdma_packet_info_t

    // @SuppressProblem -type fully_unread_static_variable -count 2 -length 3
    tdma_t  scheme;
    packet_start_t     packet_start;
    bit     packet_border;
    
    always@(negedge clk_rst.rstn) begin
       initialize(); 
    end
    
    function automatic void set_packet(tdma_packet_t packet, int index);
        if (index < 15) begin
            tdma_packet_info_data_t packet_info;
            packet_info = packet.info;
            scheme.packets[index].earliest = packet.earliest;
            scheme.packets[index].latest   = packet.latest;
            scheme.packets[index].info.id_config = sid_length_e'(packet_info.id_config);
            scheme.packets[index].info.symbol_count = packet_info.symbol_count;
        end
        else
            $fatal("TDMA packet index is too large");
    endfunction
    
    function automatic void set_header(tdma_header_t header);
        scheme.header.packet_count = header.packet_count.packet_count;
        scheme.header.period = header.period;
    endfunction

    function automatic void initialize();
        scheme.header.packet_count = 0;
        scheme.header.period = 0;
        for (int i = 0; i < 15; i++) begin
            scheme.packets[i].earliest = '0;
            scheme.packets[i].latest = '0;
            scheme.packets[i].info = '{SID_0Bit,'0};
        end
    endfunction
    
    always@(posedge i_tick_1us) begin
        packet_start.start = 1'b0;
        packet_border = 1'b0;
        for (int i = 0; i < 15; i++) begin
            if((i_current_time_in_period > scheme.packets[i].earliest) && 
               (i_current_time_in_period < scheme.packets[i].latest)) begin
                    packet_start.start = 1'b1;
                    packet_start.index = i;
            end
            if (i<14) begin
               if (i_current_time_in_period == scheme.packets[i].latest+ ((scheme.packets[i].latest - scheme.packets[i+1].earliest)/16'd2)) 
                   packet_border = 1'b1;
            end
        end
    end
    
endmodule

`endif