/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * Author        : jvoi
 * Creation date : 2023-04-03
 * Description   : interface for reading TDMA header information from TDMA buffers
 *------------------------------------------------------------------------------*/
interface spi_tdma_reader_if import spi_implementation_pkg::*; import project_pkg::*; ();
    tdma_read_action_t  action;
    logic[3:0]  index;
    logic       ready;
    data_ecc_t  data;
    
    modport master (
            output  action, index,
            input   ready, data
    );
    
    modport slave (
            input   action, index,
            output  ready, data
    );
    
endinterface : spi_tdma_reader_if