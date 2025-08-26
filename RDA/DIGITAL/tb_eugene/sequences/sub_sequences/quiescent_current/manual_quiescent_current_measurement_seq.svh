class manual_quiescent_current_measurement_seq extends quiescent_current_measurement_base_seq;
    
    `uvm_object_utils(manual_quiescent_current_measurement_seq) 
    
    function new(string name = "");
        super.new("manual_quiescent_current_measurement");
    endfunction
    
    virtual function string get_description();
        return $sformatf("Manual quiescent current measurement on channels %2b and a load of %5.2fmA", channel_bits, load_uA/1000.0);
    endfunction

    virtual task trigger_measurement();
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channel_bits[channel] == 1'b1) begin
                regmodel.DSI[channel].DSI3_channel_registers.DSI_LOAD.START_MEASUREMENT.write(status, 1);
            end
        end
    endtask
    
endclass