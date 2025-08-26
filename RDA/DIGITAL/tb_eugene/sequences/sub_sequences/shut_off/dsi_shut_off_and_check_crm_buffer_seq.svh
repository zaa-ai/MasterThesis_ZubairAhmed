interface class shut_off_strategy;

	pure virtual function string get_strategy_name();
	
	pure virtual task shut_off_channels(base_dsi_master_seq parent_sequence);
	
	pure virtual task enable_channels(base_dsi_master_seq parent_sequence);

endclass


class dsi_enable_shut_off_strategy implements shut_off_strategy;
	
	virtual function string get_strategy_name();
		return "DSI_ENABLE";
	endfunction
	
	virtual task shut_off_channels(base_dsi_master_seq parent_sequence);
		uvm_status_e status;
		#330us;
		parent_sequence.regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b00);
	endtask
	
	virtual task enable_channels(base_dsi_master_seq parent_sequence);
		uvm_status_e status;
		parent_sequence.regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
	
	static function shut_off_strategy create();
		dsi_enable_shut_off_strategy strategy = new();
		return strategy;
	endfunction
endclass

class over_temperature_shut_off_strategy implements shut_off_strategy;
	
	virtual function string get_strategy_name();
		return "over temperature";
	endfunction
	
	virtual task shut_off_channels(base_dsi_master_seq parent_sequence);
		#310us;
		parent_sequence.set_temp(175, 10us);
	endtask
	
	virtual task enable_channels(base_dsi_master_seq parent_sequence);
		uvm_status_e status;
		parent_sequence.set_temp(25, 10us);
		#50us;
		parent_sequence.regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
		parent_sequence.regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
	
	static function shut_off_strategy create();
		over_temperature_shut_off_strategy strategy = new();
		return strategy;
	endfunction
endclass

class over_voltage_shut_off_strategy implements shut_off_strategy;
	
	virtual function string get_strategy_name();
		return "over voltage";
	endfunction
	
	virtual task shut_off_channels(base_dsi_master_seq parent_sequence);
		#330us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			parent_sequence.hdl_force($sformatf(`STRING_OF(`DSI_OV_DEB_PATH), channel), 'b1);
		end
	endtask
	
	virtual task enable_channels(base_dsi_master_seq parent_sequence);
		uvm_status_e status;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			parent_sequence.hdl_release($sformatf(`STRING_OF(`DSI_OV_DEB_PATH), channel));
		end
		#100us;
		parent_sequence.regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
	
	static function shut_off_strategy create();
		over_voltage_shut_off_strategy strategy = new();
		return strategy;
	endfunction
endclass

class under_voltage_shut_off_strategy implements shut_off_strategy;
	
	virtual function string get_strategy_name();
		return "under voltage";
	endfunction
	
	virtual task shut_off_channels(base_dsi_master_seq parent_sequence);
		#330us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			parent_sequence.hdl_force($sformatf(`STRING_OF(`DSI_UV_DEB_PATH), channel), 'b1);
		end
	endtask
	
	virtual task enable_channels(base_dsi_master_seq parent_sequence);
		uvm_status_e status;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			parent_sequence.hdl_release($sformatf(`STRING_OF(`DSI_UV_DEB_PATH), channel));
		end
		#100us;
		parent_sequence.regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
	
	static function shut_off_strategy create();
		under_voltage_shut_off_strategy strategy = new();
		return strategy;
	endfunction
endclass

class ldo_shut_off_strategy implements shut_off_strategy;
	
	virtual function string get_strategy_name();
		return "LDO disable";
	endfunction
	
	virtual task shut_off_channels(base_dsi_master_seq parent_sequence);
		uvm_status_e status;
		#330us;
		parent_sequence.regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b0);
	endtask
	
	virtual task enable_channels(base_dsi_master_seq parent_sequence);
		uvm_status_e status;
		parent_sequence.regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO.write(status, 1'b1);
		parent_sequence.regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11);
	endtask
	
	static function shut_off_strategy create();
		ldo_shut_off_strategy strategy = new();
		return strategy;
	endfunction
endclass

class dsi_shut_off_and_check_crm_buffer_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_shut_off_and_check_crm_buffer_seq) 
    
	function new(string name = "");
		super.new("dsi_shut_off_and_check_crm_buffer");
	endfunction
	
	virtual task run_tests();
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b0;
		checker_config::get().disable_all_master_transmission_checkers();
		
		do_shut_off(dsi_enable_shut_off_strategy::create());
		do_shut_off(over_temperature_shut_off_strategy::create());
		do_shut_off(over_voltage_shut_off_strategy::create());
		do_shut_off(under_voltage_shut_off_strategy::create());
		do_shut_off(ldo_shut_off_strategy::create());
		
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b1;
		checker_config::get().enable_all_master_transmission_checkers();
	endtask

	virtual task do_shut_off(shut_off_strategy strategy);
		spi_read_crm_data_packets_seq read1, read2, read3;
		dsi3_crm_packet packets[project_pkg::DSI_CHANNELS-1:0][$];
		
		log_sim_description($sformatf("switch off channel during CRM using %s", strategy.get_strategy_name()), LOG_LEVEL_SEQUENCE);
		
		reset();
		#200us;
				
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			repeat(3) begin
				create_valid_CRM_packets_with_data(packets[channel], 2'(1 << channel));
			end
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;
		
		fork
			begin
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			begin
				strategy.shut_off_channels(this);
			end
			#500us;	
		join
		
		strategy.enable_channels(this);
		
		`spi_frame_begin
			`spi_frame_send(read1, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read1.expect_flags( 2'(channel), packets[channel][0].crc_correct ? {} : {CRC});
			read1.expect_packet(2'(channel), packets[channel][0]);
		end

		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;

		`spi_frame_begin
			`spi_frame_send(read2, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read2.expect_flags( 2'(channel), packets[channel][2].crc_correct ? {} : {CRC});
			read2.expect_packet(2'(channel), packets[channel][2]);
		end

		`spi_frame_begin
			`spi_frame_send(read3, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read3.expect_empty( 2'(channel));
		end
			
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
	endtask
endclass