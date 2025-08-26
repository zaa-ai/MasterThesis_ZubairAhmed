/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : dsi3_sync_master.sv
 * Author        : jvoi
 * Creation date : 2023-05-08
 * Description   : block responsible to generate SYNC pulse at 
 *------------------------------------------------------------------------------*/
module dsi3_sync_master import dsi3_pkg::*; import project_pkg::*; (
        clk_reset_if.slave  clk_rst,
        input   logic       i_fire,
        input   logic       i_tick_1us,
        input   logic       i_sync_master,
        output  logic       o_syncb_out
    );
    
    logic [3:0] counter, counter_next;
    logic   syncb_next;
    
    typedef enum logic {
        IDLE, FIRE
    } master_fire_state_t;
    
    master_fire_state_t state, state_next;
    
    always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
        if (clk_rst.rstn == 1'b0) begin
            state       <= IDLE;
            o_syncb_out <= 1'b0;
            counter     <= '0;
        end
        else begin
            state       <= state_next;
            o_syncb_out <= syncb_next;
            counter     <= counter_next;
        end
    end
    
    always_comb begin
        state_next = state;
        counter_next = counter;
        syncb_next = o_syncb_out;
        case (state)
            IDLE: begin
                if ((i_fire == 1'b1) && (i_sync_master == 1'b1)) begin
                    counter_next = 4'd11;
                    syncb_next = 1'b1;
                    state_next = FIRE;
                end
            end
            FIRE: begin
                if(i_tick_1us == 1'b1) counter_next = counter - 4'd1;
                if(i_fire == 1'b1) counter_next = 4'd11;
                if (counter == '0) begin
                    syncb_next = 1'b0;
                    state_next = IDLE;
                end
            end
        endcase
    end
    
endmodule