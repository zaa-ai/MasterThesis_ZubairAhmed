class crm_disable_clock_ref_during_transmission_p52143_697_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_disable_clock_ref_during_transmission_p52143_697_seq)
	
	function new(string name = "");
		super.new("crm_disable_clock_ref_during_transmission_p52143_697");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("disable clock ref during CRM master transmission", LOG_LEVEL_SEQUENCE);

		checker_config::get().enable_hardware_error_check = 1'b0;
		checker_config::get().expect_CRM_clock_ref_error_in_dsi_packet = 1'b1;
		
		disable_clock_ref_during_crm_transmission(0, 1ms);
		disable_clock_ref_during_crm_transmission(0, 10us);
		disable_clock_ref_during_crm_transmission(200, 1ms);
		
		checker_config::get().enable_hardware_error_check = 1'b1;
		checker_config::get().expect_CRM_clock_ref_error_in_dsi_packet = 1'b0;
	endtask
		
	task disable_clock_ref_during_crm_transmission(int channel_shift, time clk_ref_shutoff_duration);
		dsi3_crm_packet packets[$];
		spi_read_crm_data_packets_seq read;
		dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_32US;
			
		log_sim_description($sformatf("disable clock ref during CRM master transmission, channel shift = %0d, clkref shutoff duration = %0d us", channel_shift, clk_ref_shutoff_duration/1us), LOG_LEVEL_OTHERS);
		
		clear_all_irqs();
		
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, bit_time);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, 16'd1500);
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi3_crm_packet next_packet = new();
			if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
			packets.push_back(next_packet);
			add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1), 3, bit_time));
		end
		
		check_intb(1'b1);
		
		`spi_frame_begin
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01; wait_time == 15'(1*channel_shift);)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time == 15'(2*channel_shift);)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end	
		
		#100us;
		fork
			begin
				set_clk_ref(0);
			end
			begin
				#(clk_ref_shutoff_duration);
				set_clk_ref(500_000);
			end
		join_any
		
		#1100us;
		check_intb(1'b0);
		registers.check_flag(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.CLKREF, 1'b1);	

		#(3 * channel_shift * 1us);
		#500us;
		
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end_with_status({NT0, NT1, CR1, CR0})
			
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi_response_flags expected_flags[$] = {CE};
			if(!packets[channel].crc_correct) expected_flags.push_back(CRC);
			read.expect_flags( 2'(channel), expected_flags);
			read.expect_packet(2'(channel), packets[channel]);
		end
		
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		#100us;
	endtask
endclass