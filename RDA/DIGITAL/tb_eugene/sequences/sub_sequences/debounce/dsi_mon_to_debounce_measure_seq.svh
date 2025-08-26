class dsi_mon_to_debounce_measure_seq extends debounce_measure_seq;
	
	rand int channel;
	
	`uvm_object_utils(dsi_mon_to_debounce_measure_seq)

	function new(string name = "dsi_mon_to_debounce_measure");
		super.new(name);
		parameter_name = "t__DSImon,TO__";
		debounce_min = 2ms;
		debounce_max = 7ms;
	endfunction
	
	virtual task prepare_condition();
		#200us;
		clear_all_irqs();
		condition = $sformatf("voltage monitoring timeout at channel %0d", channel);
		regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.write(status, 16'd0);
		regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.DSIUV.write(status, 16'd1);
	endtask
	
	virtual function time get_time_unit();
		return 1.0ms;
	endfunction
	
	virtual task apply_condition();
		set_dsi_uv_for_channel(channel, 1);
	endtask
	
	virtual task release_condition();
		set_dsi_uv_for_channel(channel, 0);
	endtask

	virtual task wait_for_condition();
		if(get_intb() == 1'b1) @(negedge intb.D);
	endtask
	
	virtual task finalize();
		regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
endclass