class base_upload_tdma_schemes_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(base_upload_tdma_schemes_seq)
	
	function new(string name = "base_upload_tdma_schemes");
		super.new(name);
	endfunction : new
	
	virtual task run_tests();
		`uvm_error(get_type_name(), "this sequence is not intented to be executed, you should derive a sub class!")
	endtask
	
	// invalidate any uploaded TDMA schemes		
	task invalidate_all_tdma_schemes(bit sci_already_set);
		`spi_frame_begin
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#10us;
		check_tdma_upload_status(2'b00, sci_already_set);
	endtask
	
	// check that given channels have a valid TDMA scheme
	task check_tdma_upload_status(logic[1:0] channels, bit sci_is_set);
		spi_status_word_flags status_flags[$];
		if(channels[0] == 1'b0) status_flags.push_back(NT0);
		if(channels[1] == 1'b0) status_flags.push_back(NT1);
        if (sci_is_set == 1'b1) begin
		    status_flags.push_back(SCI);
        end
            
		`spi_frame_begin
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end_with_status(status_flags)
	endtask
	
	// check PDCM_PERIOD registers of given channels for given period value
	task check_pdcm_periods(logic[1:0] channels, int pdcm_period);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel] == 1'b1) begin
				registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.PDCM_PERIOD, pdcm_period);
			end
		end
    endtask
    
    virtual task clear_cmd_ign_irq(project_pkg::dsi_logic_t channels);
        if (channels == '0) begin
            regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status,1);
        end
    endtask
endclass


class upload_random_valid_tdma_schemes_seq extends base_upload_tdma_schemes_seq;

	`uvm_object_utils(upload_random_valid_tdma_schemes_seq)
	
	function new(string name = "");
		super.new("upload_random_valid_tdma_schemes");
	endfunction : new
	
	virtual task run_tests();

		log_sim_description("upload random valid TDMA scheme on all channels", LOG_LEVEL_SEQUENCE);
		
		repeat(100) begin
			upload_tdma_scheme_seq upload_seq;
			tdma_scheme_pdcm scheme = new();
			if(!scheme.randomize() with {packets.size() > 0;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			
			invalidate_all_tdma_schemes(1'b0);
			#10us;
					
			`uvm_create(upload_seq)
			if(!upload_seq.randomize()) `uvm_error(get_type_name(), "failed to randomize");
			upload_seq.scheme = scheme;
			
			log_sim_description($sformatf("uploading TDMA scheme with %0d packets at channels %2b", scheme.get_packet_count(), upload_seq.channels), LOG_LEVEL_OTHERS);
			`uvm_send(upload_seq)
			
			#50us;
			check_tdma_upload_status(upload_seq.channels, (upload_seq.channels=='0));
			check_pdcm_periods(upload_seq.channels, scheme.pdcm_period);
            clear_cmd_ign_irq(upload_seq.channels);
			#50us;
		end
		invalidate_all_tdma_schemes(1'b0);
	endtask
endclass