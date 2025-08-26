class shut_off_seq extends base_dsi_master_seq;

	`uvm_object_utils(shut_off_seq)

	function new(string name = "");
		super.new("shut_off");
	endfunction

	virtual task run_tests();
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b0;
		
		log_sim_description("Testcases for shutting down transceiver e.g. overtemperature, overvoltage and undervoltage", LOG_LEVEL_TOP);
		
		`create_and_send(dsi_enable_ignore_new_commands_seq)
		`create_and_send(dsi_enable_abort_crm_seq)
		`create_and_send(dsi_enable_abort_pdcm_seq)
		`create_and_send(dsi_enable_abort_multi_packet_pdcm_seq)
		`create_and_send(dsi_enable_abort_discovery_mode_seq)
		`create_and_send(dsi_enable_abort_command_queue_seq)
		
		checker_config::get().disable_all_master_transmission_checkers();
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b0;
		
		checker_config::get().enable_hardware_error_check = 1'b0;
		overtemperature_shut_off_crm();
		overtemperature_shut_off_pdcm();
		overvoltage_shut_off_crm();
		overvoltage_shut_off_pdcm();
		undervoltage_shut_off_crm();
		undervoltage_shut_off_pdcm();
		
		disable_ldo_crm();
		disable_ldo_pdcm();
		measure_temperature_debouncing();
		
		`create_and_send(overtemperature_status_seq)
		`create_and_send(dsi_shut_off_and_check_crm_buffer_seq)
		`create_and_send(dsi_shut_off_and_check_pdcm_buffer_seq)
		
		get_checker_config().enable_hardware_error_check = 1'b1;
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b1;
		checker_config::get().enable_all_master_transmission_checkers();
	endtask
	
	task overtemperature_shut_off_crm();
	  `create_and_send_with(overtemperature_shut_off_seq, time_after_dsi_transmit == 160us; time_before_dsi_transmit == 400us; active_channels == 2'b11; use_pdcm == 1'b0;)
	  `create_and_send_with(overtemperature_shut_off_seq, time_after_dsi_transmit == 400us; time_before_dsi_transmit ==   0us; active_channels == 2'b11; use_pdcm == 1'b0;)
	  `create_and_send_with(overtemperature_shut_off_seq, time_after_dsi_transmit == 310us; time_before_dsi_transmit == 400us; active_channels == 2'b11; use_pdcm == 1'b0;)
	endtask
	
	task overtemperature_shut_off_pdcm();
	  `create_and_send_with(overtemperature_shut_off_seq, time_after_dsi_transmit ==  80us; time_before_dsi_transmit == 300us; active_channels == 2'b11; use_pdcm == 1'b1;)
	  `create_and_send_with(overtemperature_shut_off_seq, time_after_dsi_transmit == 300us; time_before_dsi_transmit ==   0us; active_channels == 2'b11; use_pdcm == 1'b1;)
	  `create_and_send_with(overtemperature_shut_off_seq, time_after_dsi_transmit == 330us; time_before_dsi_transmit ==   0us; active_channels == 2'b11; use_pdcm == 1'b1;)
	endtask
	
	task overvoltage_shut_off_crm();
    	`create_and_send_with(voltage_shut_off_seq, uv_n_ov == 1'b0; wait_time_add == 0; time_after_dsi_transmit == 130us; time_before_dsi_transmit == 0us; active_channels == 2'b11; use_pdcm == 1'b0;)
	endtask
	
	task overvoltage_shut_off_pdcm();
		`create_and_send_with(voltage_shut_off_seq, uv_n_ov == 1'b0; wait_time_add == 600; time_after_dsi_transmit == 80us; time_before_dsi_transmit == 0us; active_channels == 2'b11; use_pdcm == 1'b1;)
	endtask
	
	task undervoltage_shut_off_crm();
	    `create_and_send_with(voltage_shut_off_seq, uv_n_ov == 1'b1; wait_time_add == 0; time_after_dsi_transmit == 130us; time_before_dsi_transmit == 0us; active_channels == 2'b11; use_pdcm == 1'b0;)
	endtask
	
	task undervoltage_shut_off_pdcm();
		`create_and_send_with(voltage_shut_off_seq, uv_n_ov == 1'b1; wait_time_add == 800; time_after_dsi_transmit == 80us; time_before_dsi_transmit == 0us; active_channels == 2'b11; use_pdcm == 1'b1;)
	endtask
	
	task disable_ldo_crm();
		`create_and_send_with(ldo_disable_shut_off_seq, time_after_dsi_transmit == 600us; time_before_dsi_transmit == 0us; active_channels == 2'b11; use_pdcm == 1'b0;)
	endtask
	
	task disable_ldo_pdcm();
		`create_and_send_with(ldo_disable_shut_off_seq, time_after_dsi_transmit == 400us; time_before_dsi_transmit == 0us; active_channels == 2'b11; use_pdcm == 1'b1;)
	endtask
	
	task measure_temperature_debouncing();
		dsi3_master_config _config = get_dsi3_master_config(0);
		time times[3];
		log_sim_description("measure overtemperature debouncing", LOG_LEVEL_SEQUENCE );
		times[0] = $time();
		set_temp(175, 0.1us);
		@(negedge _config.vif.cable.Voltage);
		times[1] = $time();
		set_temp(25, 0.1us);
		fork
			begin
				regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1);
				regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 4'hf);
			end
			begin
				@(posedge _config.vif.cable.Voltage);
			end
		join_any
		disable fork;
		times[2] = $time();
		#5us;
		log_sim_measure("t__OT,deb__", $sformatf("%5.2f",(times[1]-times[0])/1.0us));
		log_sim_measure("t__OT,deb__", $sformatf("%5.2f",(times[2]-times[1])/1.0us));
		#100us;
	endtask
	
endclass
