/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : dsi3_iload_control.sv
 * Author        : jvoi
 * Creation date : 2023-05-04
 * Description   : Module responsible to check quiescent current of DSI3 channel
 *------------------------------------------------------------------------------*/
module dsi3_iload_control import dsi3_pkg::*; (
        clk_reset_if.slave      clk_rst,
        input   logic           i_rx_iload_cmp,
        input   logic           i_start,
        input   logic           i_tick_1us,
        
        DSI3_channel_registers_DSI_LOAD_if.slave    DSI_LOAD,
        output  logic           o_ready,
        output  logic           o_hw_fail
    );
    
    typedef enum logic[1:0] {IDLE, INITIALIZE, IDAC_SA} iload_state_type;
    iload_state_type    state, state_next;
    
    logic[3:0]  counter_10us, counter_10us_next;
    logic counted_10us;
    assign counted_10us = ((counter_10us == 4'd9) && (i_tick_1us == 1'b1)) ? 1'b1 : 1'b0;
    
    logic[2:0]  dac_bit_counter, dac_bit_counter_next;
    
    
    always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
        if (clk_rst.rstn == 1'b0)  begin
            counter_10us <= '0;
            state        <= IDLE;
            dac_bit_counter <= '1;
        end
        else begin
            state       <= state_next;
            if (i_tick_1us == 1'b1) begin
                counter_10us <= counter_10us_next;
                dac_bit_counter <= dac_bit_counter_next;
            end
        end
    end
    
    logic   start_by_register_write;
    assign  start_by_register_write = DSI_LOAD.START_MEASUREMENT;
    assign  DSI_LOAD.START_MEASUREMENT_in = 1'b0;
    always_comb begin
        if (DSI_LOAD.START_MEASUREMENT == 1'b1) begin
            DSI_LOAD.START_MEASUREMENT_set = 1'b1;
        end
        else begin
            DSI_LOAD.START_MEASUREMENT_set = 1'b0; 
        end
    end
    
    always_comb begin
        state_next = state;
        DSI_LOAD.LOAD_in = DSI_LOAD.LOAD;
        DSI_LOAD.LOAD_set = 1'b0;
        DSI_LOAD.IDLE_in = DSI_LOAD.IDLE;
        DSI_LOAD.IDLE_set = 1'b0;
        
        dac_bit_counter_next = dac_bit_counter;
        counter_10us_next = counter_10us;
        o_ready = 1'b0;
        
        o_hw_fail = 1'b0;
        
        case (state)
            IDLE: begin
                o_ready = 1'b1;
                if((i_start == 1'b1) || (start_by_register_write == 1'b1)) begin
                    state_next = INITIALIZE;
                    DSI_LOAD.IDLE_in = 1'b0;
                    DSI_LOAD.IDLE_set = 1'b1;
                end
            end
            INITIALIZE : begin
                counter_10us_next = counter_10us + 4'(i_tick_1us);
                dac_bit_counter_next = '1;
                DSI_LOAD.LOAD_set = 1'b1;
                DSI_LOAD.LOAD_in = '0; 
                if (counted_10us == 1'b1) begin
                    state_next = IDAC_SA;
                    counter_10us_next = '0;
                    DSI_LOAD.LOAD_in = '0;
                    dac_bit_counter_next = 3'd4;
                end
            end
            IDAC_SA: begin
                counter_10us_next = counter_10us + 4'(i_tick_1us);
                DSI_LOAD.LOAD_set = 1'b1;
                DSI_LOAD.LOAD_in[dac_bit_counter] = 1'b1; 
                if (counted_10us == 1'b1) begin
                    dac_bit_counter_next = dac_bit_counter - 3'd1;
                    DSI_LOAD.LOAD_in[dac_bit_counter] = i_rx_iload_cmp;
                    if (dac_bit_counter == '0) begin
                        DSI_LOAD.IDLE_in = 1'b1;
                        DSI_LOAD.IDLE_set = 1'b1;
                        state_next = IDLE;
                    end
                    counter_10us_next = '0;
                end
                
            end
            default: begin
                o_hw_fail = 1'b1;
                state_next = IDLE;
                counter_10us_next = '0;
            end
        endcase
    end
    
endmodule
