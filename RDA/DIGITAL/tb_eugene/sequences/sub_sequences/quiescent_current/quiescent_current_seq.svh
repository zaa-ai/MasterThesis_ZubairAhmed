class quiescent_current_seq extends quiescent_current_measurement_base_seq;
    
    `uvm_object_utils(quiescent_current_seq) 
    
    function new(string name = "");
        super.new("quiescent_current_measurement_by_command");
    endfunction
    
    virtual function string get_description();
        return $sformatf("Quiescent current measurement on channels %2b and a load of %5.2fmA", channel_bits, load_uA/1000.0);
    endfunction

    virtual task trigger_measurement();
        spi_measure_quiescent_current_seq   iload_seq;
        `spi_frame_begin
            `spi_frame_send(iload_seq, channel_bits == local::channel_bits;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
    endtask
    
endclass