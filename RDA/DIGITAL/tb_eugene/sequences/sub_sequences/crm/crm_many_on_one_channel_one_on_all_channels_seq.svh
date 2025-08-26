class crm_many_on_one_channel_one_on_all_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_many_on_one_channel_one_on_all_channels_seq)
	
	function new(string name = "");
		super.new("crm_many_on_one_channel_one_on_all_channels");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("multiple CRMs on one channel and one on all channels in a single SPI frame", LOG_LEVEL_SEQUENCE);
		
		transaction_recorder.clear_all();

		repeat(20) begin
			add_slave_crm_scheme(0, tdma_scheme_crm::no_answer());
		end
		add_slave_crm_scheme(0, tdma_scheme_crm::no_answer());
		add_slave_crm_scheme(1, tdma_scheme_crm::no_answer());
		
		`spi_frame_begin
			repeat(20) begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b1;)
			end
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#10ms;
	endtask
endclass