class sync_master_crm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(sync_master_crm_seq) 
	
	function new(string name = "");
		super.new("sync_master_crm");
	endfunction
	
	virtual task run_tests();
		log_sim_description("sync CRM and using SYNCB master feature", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		set_syncb(1'b0);
		#10us;
		expect_SYNC_IDLE_REG('0, 1'b0);
        
        set_syncb(1'bz);
		
		transaction_recorder.clear_all();
        registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_MASTER, 1);
        
		`spi_frame_begin
			`spi_frame_create(spi_dsi_wait_seq, wait_time == 100; channel_bits == 2'b01;)
			`spi_frame_create(spi_dsi_wait_seq, wait_time == 200; channel_bits == 2'b10;)
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#10us;
		expect_SYNC_IDLE_REG(2'b11, 1'b0);
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
    		expect_SYNC(i, 2'b00, 1'b0);
        end
        
        #100us;
        
		expect_SYNC_IDLE_REG(2'b10, 1'b0);
		expect_SYNC(0, 2'b11, 1'b1);
		expect_SYNC(1, 2'b00, 1'b0); // SYNC not yet registered, command still in queue
        
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			transaction_recorder.expect_tr_count(i, 0);
        end
        
        fork
            begin
        		#100us;
        		expect_SYNC_IDLE_REG(2'b11, 1'b0); // both channels busy, PIN is LOW
                #1.5ms;
                `uvm_error(this.get_type_name(), $sformatf("No pulse at SYNCB pin detected!"))
            end
            begin
                time pulse_start, pulse_end;
                @(posedge syncb_out.D) pulse_start = $time();
                @(negedge syncb_out.D) pulse_end   = $time();
                begin
                    time pulse_time;
                    epm_t__DSI3_master_sync__ epm = edf_parameters.epms.t__DSI3_master_sync__;
                    pulse_time = (pulse_end - pulse_start);
                    if ((pulse_time < epm.get_min_time()) || (pulse_time > epm.get_max_time())) begin
                       string time_unit = epm.unit; 
                        `uvm_error(this.get_type_name(), $sformatf("Parameter %s is not measured correctly! Got %6.2f%s but expected to be inside %6.2f%s ... %6.2f%s", 
                                epm.name, pulse_time / 1.0us, time_unit, epm.get_min, time_unit, epm.get_max, time_unit))
                    end
                    log_sim_measure(epm.name,$sformatf("%6.2f", (pulse_time / epm.get_time_scale)));
                end
                #500us;
            end
        join_any
        disable fork;
        
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			transaction_recorder.expect_tr_count(i, 1);
			expect_SYNC(i, 2'b00, 1'b0);
            expect_SYNC_IDLE_REG(2'b00, 1'b0);
		end
		
		transaction_recorder.disable_recorder();
        registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_MASTER, 0);
        #10us;
	endtask
endclass