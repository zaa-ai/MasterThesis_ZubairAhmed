/**
 * Class: ecc_dsi3_crm_data_buffer_error_seq
 * 
 * Super sequence for applying ecc errors in DSI3 command blocks
 */
class ecc_dsi3_crm_data_buffer_error_seq #(int bit_width=8) extends ecc_error_base_seq;
	
	`uvm_object_param_utils(ecc_dsi3_crm_data_buffer_error_seq #(bit_width))
	
	function new(string name = "");
		super.new(name);
	endfunction
	
	virtual function void initialize();
		irq_stat_ecc_field = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_STAT.DSI_CRM_DATA_BUF;
		irq_stat_ecc_corr_field = regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF;
	endfunction
	
	virtual task apply_stimuli();
		bit all_channels_correct = (bit_error != TWO_BIT_ERR) ? 1'b1 : 1'b0;
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == local::all_channels_correct; bad_channel == local::channel;)
	endtask
	
	virtual task apply_error();
        virtual dsi3_slave_if vif = get_dsi3_master_config(channel).vif;
        fork
            begin
                @(negedge vif.cable.Voltage);
                @(vif.cable.Current)
                #40us;
            end
            begin
                #10ms;
                `uvm_error(this.get_type_name(), $sformatf("DSI3 voltage or current did not toggle on channel %1d", channel))
            end
        join_any
        disable fork;
		apply_ecc_failure();
        #100ns;
        remove_ecc_failure();
		#20us;
		if (bit_error == TWO_BIT_ERR)	check_HE_ic_status(1'b1);
		else 							check_HE_ic_status(1'b0);
	endtask
	
	virtual task apply_ecc_failure();
		random_data_error#(bit_width)	data_error;
		uvm_hdl_data_t			data_read;
		
		if (! uvm_hdl_read(path, data_read)) `uvm_error(this.get_type_name(), $sformatf("Read on %s failed!", path))
		`uvm_info(this.get_type_name(), $sformatf("read %s with %2h", test, data_read[bit_width-1:0]), UVM_INFO)
		data_error = new(data_read[bit_width-1:0], bit_error);
		if (!data_error.randomize()) begin
			`uvm_error(this.get_type_name(), "randomization of data_error failed")
		end
		
		`uvm_info(this.get_type_name(), $sformatf("force %s with %2h", test, data_error.get_data()), UVM_INFO)
		`uvm_info(this.get_type_name(), $sformatf("force %s with %2h", path, data_error.get_data()), UVM_INFO)
		if (! uvm_hdl_deposit(path, data_error.get_data())) `uvm_error(this.get_type_name(), $sformatf("Force on %s failed!", path))
    endtask
    
    virtual task remove_ecc_failure();
        `uvm_info(this.get_type_name(), $sformatf("release %s", path), UVM_INFO)
        if (! uvm_hdl_release(path)) `uvm_error(this.get_type_name(), $sformatf("Release %s failed!", path))
    endtask
	
	virtual task run_check_after_error();
		check_HE_ic_status(1'b0);
		`create_and_send_with(single_crm_on_all_channels_seq, all_channels_correct == 1'b1;)
        `create_and_send_with(single_pdcm_on_all_channels_seq, all_channels_correct == 1'b1;)
	endtask

endclass

/**
 * Class: ecc_dsi3_crm_data_buffer_fsm_seq
 * 
 * sequence for applying ECC errors in DSI3 data buffer FSM
 */
class ecc_dsi3_crm_data_buffer_fsm_seq extends ecc_dsi3_crm_data_buffer_error_seq#(9);
	
	`uvm_object_utils(ecc_dsi3_crm_data_buffer_fsm_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_crm_data_buffer_fsm_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_CRM_DATA_BUFFER_FSM_STATE, channel);
		test = "DSI3 data buffer FSM state";
	endfunction
	
endclass


/**
 * Class: ecc_dsi3_crm_data_buffer_read_pointer_seq
 * 
 * sequence for applying ECC errors in DSI3 data buffer read pointer
 */
class ecc_dsi3_crm_data_buffer_read_pointer_seq extends ecc_dsi3_crm_data_buffer_error_seq#(7);

	`uvm_object_utils(ecc_dsi3_crm_data_buffer_read_pointer_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_crm_data_buffer_read_pointer_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_CRM_DATA_BUFFER_READ_POINTER, channel);
		test = "DSI3 data buffer read pointer";
	endfunction
	
endclass

/**
 * Class: ecc_dsi3_crm_data_buffer_write_pointer_seq
 * 
 * sequence for applying ECC errors in DSI3 data buffer write pointer
 */
class ecc_dsi3_crm_data_buffer_write_pointer_seq extends ecc_dsi3_crm_data_buffer_error_seq#(7);

	`uvm_object_utils(ecc_dsi3_crm_data_buffer_write_pointer_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_crm_data_buffer_write_pointer_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_CRM_DATA_BUFFER_WRITE_POINTER, channel);
		test = "DSI3 data buffer write pointer";
	endfunction
	
endclass

/**
 * Class: ecc_dsi3_crm_data_buffer_valid_pointer_seq
 * 
 * sequence for applying ECC errors in DSI3 data buffer valid pointer
 */
class ecc_dsi3_crm_data_buffer_valid_pointer_seq extends ecc_dsi3_crm_data_buffer_error_seq#(7);

	`uvm_object_utils(ecc_dsi3_crm_data_buffer_valid_pointer_seq)
	
	function new(string name = "");
		super.new("ecc_dsi3_crm_data_buffer_valid_pointer_seq");
	endfunction
	
	virtual function void initialize();
		super.initialize();
		path = $sformatf(PATH_DSI3_CRM_DATA_BUFFER_VALID_POINTER, channel);
		test = "DSI3 data buffer valid pointer";
	endfunction
	
endclass
