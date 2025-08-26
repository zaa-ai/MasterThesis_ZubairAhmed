/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : general_data_writer_inputs.sv
 * Author        : jvoi
 * Creation date : 2023-05-12
 * Description   : interface containing general signals for all data writers
 *------------------------------------------------------------------------------*/
interface general_data_writer_inputs_if;
    import project_pkg::*;
    logic   transceiver_enable_negedge;
    logic   response_finished;
    logic   received_data;
    logic   start_transmit;
    logic   rec_pending;
    logic   rec_pending_posedge;
    logic   rec_pending_negedge;
    
    logic   symbol_count_overflow;
    logic   symbol_error_set;
    
    logic   ov, uv;
    
    logic[8:0] symbol_count;
    data_ecc_t      rx_data;
    data_t          rx_data_corrected;
    
    timebase_t  time_of_start_transmit;
    timebase_t  time_of_start_receive_after_command;
    
    modport slave (
        input   transceiver_enable_negedge, response_finished, received_data,
        input   start_transmit, rec_pending, rec_pending_negedge, rec_pending_posedge,
        input   symbol_count_overflow, symbol_count, symbol_error_set,
        input   time_of_start_transmit, time_of_start_receive_after_command,
        
        input   uv, ov,
        input   rx_data, rx_data_corrected
    );
    
endinterface