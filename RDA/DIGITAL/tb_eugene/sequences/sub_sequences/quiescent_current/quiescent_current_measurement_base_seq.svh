/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * Author        : jvoi
 * Creation date : 2023-06-26
 * Description   :
 *------------------------------------------------------------------------------*/
virtual class quiescent_current_measurement_base_seq extends base_dsi_master_seq;
    
    rand bit[1:0]   channel_bits;
    rand int unsigned load_uA;
    
    constraint co_load {load_uA < 5000;}
    
    function new(string name = "");
        super.new(name);
    endfunction
    
    virtual task run_tests();
        uvm_reg_data_t  previous_value[project_pkg::DSI_CHANNELS-1:0];
        
        log_sim_description(get_description(), LOG_LEVEL_OTHERS);
        
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channel_bits[channel] == 1'b1) begin
                set_iload(load_uA/1000.0, channel);
                regmodel.DSI[channel].DSI3_channel_registers.DSI_LOAD.LOAD.read(status, previous_value[channel]);
            end
        end
        
        #1us;
        
        check_idle_flag(1'b1);
        
        trigger_measurement();
        
        #10us;
        check_idle_flag(1'b0);
        #200us;
        
        check_idle_flag(1'b1);
        check_idac_value();
        #10us;
    endtask
    
    pure virtual function string get_description();
    pure virtual task trigger_measurement();
    
    virtual task check_idle_flag(bit value);
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channel_bits[channel] == 1'b1)
                registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_LOAD.IDLE, value);
            else
                registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_LOAD.IDLE, 1'b1);
        end
    endtask
    
    virtual task check_idac_value();
        for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            if (channel_bits[channel] == 1'b1) begin
                uvm_reg_data_t  value;
                int expected_value = int'(load_uA / 145.0);
                if (expected_value > 'h1f) expected_value = 'h1f;
                regmodel.DSI[channel].DSI3_channel_registers.DSI_LOAD.LOAD.read(status, value);
                if (expected_value == 0) begin
                    if ((value[31:0] > expected_value + 1))
                        report_error(channel, value, expected_value);
                end
                else begin
                    if ((value[31:0] < expected_value - 1) || (value[31:0] > expected_value + 1))
                        report_error(channel, value, expected_value);
                end
            end
        end
    endtask
    
    virtual function void report_error(int channel, uvm_reg_data_t value, int expected_value);
        `uvm_error(this.get_type_name(), $sformatf("Load current is not correct at channel %1d! Expected %1d (+-1) but got %1d", channel, expected_value, value))
    endfunction
    
endclass