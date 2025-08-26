class p52144_215_seq extends base_dsi_master_seq;

	`uvm_object_utils(p52144_215_seq)

	function new(string name = "");
		super.new("p52144_215");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		int clk_delay = 0; 
		
		log_sim_description("Testcase for Jira Issue P52144-215", LOG_LEVEL_TOP);
		m_spi_agent.m_config.csb_handler = per_frame_csb_hander::create(); 
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 16; symbol_count_max == 16; chiptime == 4; bit_time == dsi3_pkg::BITTIME_16US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
		repeat(5000) begin
			m_spi_agent.m_config.cycle_time = 55_600ps;
			
			log_sim_description($sformatf("reset command with clk delay %0dps", clk_delay), LOG_LEVEL_SEQUENCE);
			
			read_status();
			#10us;			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_end
			#10us;
			
			@(negedge clk_osc_if_inst.clk);
			#(clk_delay * 1ps);
			
			`spi_frame_begin
				`spi_frame_create(spi_reset_seq, last_bit == 1'b1;)
			`spi_frame_end
			
			#10us;
			read_status();
			#10us;
			read_status();
			#10us;
			read_status();
			#100us;	
			clk_delay += 500;
		end
	endtask
	
	task read_status();
		`spi_frame_begin
			`spi_frame_create(spi_read_status_seq, filler == 16'h0000;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; filler == 16'h0000;)
		`spi_frame_end_with_status({})
	endtask
endclass

