/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : frame_data_visualizer.sv
 * Author        : jvoi
 * Creation date : 2023-04-19
 * Description   :
 *------------------------------------------------------------------------------*/
module frame_data_visualizer #() (
        clk_reset_if.slave              clk_rst,
        pdcm_buffer_writer_if.slave     pdcm_data_writer
    );
    
    import project_pkg::*;
    import buffer_if_pkg::*;
    
    typedef struct {
        PACKET_STAT_t   header;
        data_t          data[64];
    } packet_t;
    
    typedef struct {
        FRAME_STAT_t    header;
        packet_t        packets[15];
    } frame_t;
    
//    frame_t  frames[];
    
    frame_t     new_frame;
    packet_t    new_packet;
    // @SuppressProblem -type fully_unread_static_variable -count 1 -length 1
    int         packet_index, word_index, frame_index;
    bit         invalidate_next;
    
    always@(negedge clk_rst.rstn) begin
        clear_frame_data();
        reset_new_frame();
        reset_new_packet();
    end
    
    function automatic void clear_frame_data();
//        frames.delete();
        frame_index = 0;
    endfunction
    
    function automatic void reset_new_frame();
        packet_index = 0;
        new_frame.header = '0;
        foreach(new_frame.packets[i]) begin
            foreach(new_frame.packets[i].data[k])
                new_frame.packets[i].data[k] = '0;
            new_frame.packets[i].header = '0;
        end
        invalidate_next = 1'b0;
    endfunction
    
    function automatic void reset_new_packet();
        word_index = 0;
        new_packet.header = '0;
        foreach(new_packet.data[i])
            new_packet.data[i] = '0;
    endfunction
    
    always@(posedge clk_rst.clk) begin
        case(pdcm_data_writer.action)
            PDCM_BUFFER_WRITE: begin
                new_packet.data[word_index] = pdcm_data_writer.data.data;
                word_index++;
            end
            PDCM_BUFFER_VALIDATE: begin
//                frames[frame_index] = new_frame;
                if (invalidate_next == 1'b0) begin
                    frame_index++;
                end
                reset_new_frame();
                reset_new_packet();
                invalidate_next = 1'b0;
            end
            PDCM_BUFFER_INVALIDATE: begin
                reset_new_frame();
                reset_new_packet();
                invalidate_next = 1'b0;
            end
            PDCM_BUFFER_CLEAR: begin
                clear_frame_data();
            end
            PDCM_BUFFER_CLEAR_AND_INVALIDATE_NEXT: begin
                clear_frame_data();
                if ((word_index > 0) || (packet_index > 0))
                    invalidate_next = 1'b1;
            end
            PDCM_BUFFER_WRITE_PACKET_HEADER: begin
                if (new_packet.header == '0)
                    new_packet.header = pdcm_data_writer.data.data;
                else begin
                    new_frame.packets[packet_index]= new_packet;
                    reset_new_packet();
                    packet_index++;
                    new_packet.header = pdcm_data_writer.data.data;
                end
            end
            PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN: begin
                new_packet.header = pdcm_data_writer.data.data;
                new_frame.packets[packet_index]= new_packet;
                reset_new_packet();
                packet_index++;
            end
            PDCM_BUFFER_WRITE_FRAME_HEADER: begin
                new_frame.header = pdcm_data_writer.data.data;
            end
            PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN: begin
                new_frame.header = pdcm_data_writer.data.data;
            end
        endcase
    end
    
endmodule