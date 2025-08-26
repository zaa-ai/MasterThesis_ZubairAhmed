class dsi_uv_debounce_measure_seq extends debounce_measure_seq;
	
	rand int channel;
	
	`uvm_object_utils(dsi_uv_debounce_measure_seq)

	function new(string name = "dsi_uv_debounce_measure_seq");
		super.new(name);
		parameter_name = "t__DSI,OVUV,deb__";
		debounce_min = 1ns;
		debounce_max = 100ns;
		do_measure = 1'b0; // this parameter has been removed in 521.43
	endfunction
	
	virtual task prepare_condition();
		clear_all_irqs();
		condition = $sformatf("UV timeout at channel %0d", channel);
		regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.write(status, 16'd0);
		regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.DSIUV.write(status, 16'd1);
	endtask
	
	virtual task apply_condition();
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#20us;
		set_dsi_uv_for_channel(channel, 1);
	endtask
	
	virtual task release_condition();
		set_dsi_uv_for_channel(channel, 0);
	endtask

	virtual task wait_for_condition();
		spi_read_crm_data_packets_seq read;
		wait_for_dab();
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b01 << channel;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		if(read.get_data_packet(channel).get_value(VE) == 1'b0) begin
			#1ms; // just wait to run into check timeout
		end
	endtask
	
	virtual task finalize();
		regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
endclass