/*------------------------------------------------------------------------------
 * File          : pdcm_frame_reader.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Mar 6, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

module pdcm_frame_reader import project_pkg::*; (
        clk_reset_if.slave          clk_rst,
        packet_reader_if.slave	    reader,
        buffer_reader_if.master     data_reader,
        input   data_t              i_tdma_frame_word_count,
        ecc_error_if.master         ecc_error
);
    
    import spi_implementation_pkg::*;
    import project_pkg::*;
    import buffer_if_pkg::*;
    
    data_t	word_counter, word_counter_next;
    logic   store_word_counter;
    
    /*###   ECC_DECCODER - PDCM data reader  #######################################*/
    ecc_decoder #(
        .DATA_WIDTH(DATA_WIDTH),
        .ECC_WIDTH (ECC_WIDTH )
    ) i_ecc_dec_pdcm_rx_data (
        .i_correct_n(1'b0                  ),
        .i_data     (data_reader.data.data ),
        .i_ecc      (data_reader.data.ecc  ),
        .o_data     (                      ),
        .o_ecc_cor  (ecc_error.single_error),
        .o_ecc_err  (ecc_error.double_error));
    
    /*###   FSM   #################################################################*/
    typedef	enum logic[2:0] {IDLE, READ_DATA_NEXT, READ_DATA, READ_EMPTY_FRAME, FINISH_FRAME, DELETE_NOT_READ_DATA} packet_reader_state_t;
    packet_reader_state_t	state, state_next;
    logic   handle_finish, handle_finish_next, handle_finish_active;
    
    always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
        if (clk_rst.rstn == 1'b0) begin
            state           <= IDLE;
            handle_finish   <= 1'b0;
            word_counter    <= '0;
        end
        else begin
            state	        <= state_next;
            handle_finish   <= handle_finish_next;
            if (store_word_counter == 1'b1)
                word_counter    <= word_counter_next;
        end
    end
    
    assign  handle_finish_active = handle_finish | reader.abort;
    
    always_comb begin
        state_next = state;
        word_counter_next = word_counter;
        
        data_reader.action = IDLE_READ;
        data_reader.step = '0;
        
        reader.finished = 1'b0;
        reader.got_data = 1'b0;
        reader.data = '{'0, ECC_FOR_DATA_0};
        
        handle_finish_next = handle_finish_active;
        store_word_counter = 1'b0;
        
        case(state)
            IDLE: begin
                if (i_tdma_frame_word_count != 16'd0) begin : tdma_scheme_defined
                    if (reader.get_data == 1'b1) begin : start_read_data
                        if (data_reader.empty == 1'b1) begin : start_reading_empty_frame
                            state_next = READ_EMPTY_FRAME;
                            reader.got_data = 1'b1;
                            word_counter_next = 16'd1;
                            store_word_counter = 1'b1;
                        end
                        else begin
                            state_next = READ_DATA_NEXT;
                            word_counter_next = '0;
                            store_word_counter = 1'b1;
                        end
                    end
                    else begin 
                        if (reader.abort == 1'b1) begin
                            state_next = FINISH_FRAME;
                        end
                    end
                end
                else begin
                    if (reader.get_data == 1'b1) begin
                        reader.got_data = 1'b1;
                    end
                    else begin
                        if (reader.abort == 1'b1) begin
                            state_next = FINISH_FRAME;
                        end
                    end
                end
            end
            READ_EMPTY_FRAME: begin
                if (reader.abort == 1'b1) begin
                    state_next = FINISH_FRAME;
                end
                else begin
                    if (word_counter < i_tdma_frame_word_count) begin
                        // read next empty data
                        if (reader.get_data == 1'b1) begin
                            reader.got_data = 1'b1;
                            word_counter_next = word_counter + 16'd1;
                            store_word_counter = 1'b1;
                        end
                    end
                    // everything read
                    else begin
                        state_next = FINISH_FRAME;
                    end
                end
            end
            READ_DATA_NEXT: begin
                if (reader.abort == 1'b1) begin
                    state_next = DELETE_NOT_READ_DATA;
                end
                else begin
                    data_reader.action = BUFFER_READ;
                    if(data_reader.ready == 1'b1) begin
                        state_next = READ_DATA;
                        reader.got_data = 1'b1;
                        reader.data = data_reader.data;
                        word_counter_next = word_counter + 16'd1;
                        store_word_counter = 1'b1;
                    end
                end
            end
            READ_DATA: begin
                if (reader.abort == 1'b1) begin
                    state_next = DELETE_NOT_READ_DATA;
                end
                else begin
                    if (word_counter < i_tdma_frame_word_count) begin
                        if (data_reader.empty == 1'b1) begin
                            state_next = READ_EMPTY_FRAME;
                        end
                        else begin
                            if (reader.get_data == 1'b1) begin
                                state_next = READ_DATA_NEXT;
                            end
                        end
                    end
                    // everything read
                    else begin
                        state_next = FINISH_FRAME;
                    end
                end
            end
            DELETE_NOT_READ_DATA: begin
                data_reader.action = BUFFER_MOVE_POINTER;
                data_reader.step = i_tdma_frame_word_count - word_counter;
                if (data_reader.ready == 1'b1) begin
                    state_next = FINISH_FRAME;
                end
            end
            FINISH_FRAME: begin
                reader.finished = 1'b1;
                store_word_counter = 1'b1;
                word_counter_next = '0;
                state_next = IDLE;
            end
            
        endcase
        
    end
    
endmodule