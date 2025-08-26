class uvm_register_sequences_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(uvm_register_sequences_seq)

	typedef struct {
		uvm_reg_block block;
		bit causes_hardware_error;
	} reg_block_definition;
	
	function new(string name = "");
		super.new("uvm_register_sequences");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("UVM register sequences", LOG_LEVEL_TOP);
		new_powerup();
		uvm_register_sequences();
	endtask
	
	task new_powerup();
		// make sure that there is no CLKREF error
		hdl_force(`STRING_OF(`TRIM_OSC_PATH), 7'h4b);
		power_down();
		set_resb(1);
		fork
			set_vsup(12, 2ms);
			#3ms;
		join
		#1ms;
	endtask

	task uvm_register_sequences();
		reg_block_definition blocks[$];
		
		blocks.push_back(to_block(regmodel.Info, 1'b0));
		blocks.push_back(to_block(regmodel.DSI_common, 1'b0));
		foreach(regmodel.DSI[channel]) begin
			blocks.push_back(to_block(regmodel.DSI[channel], 1'b0));
			blocks.push_back(to_block(regmodel.DSI_CMD_STAT[channel], 1'b0));
			blocks.push_back(to_block(regmodel.DSI_CRM_STAT[channel], 1'b0));
			blocks.push_back(to_block(regmodel.DSI_PDCM_STAT[channel], 1'b0));
		end
		blocks.push_back(to_block(regmodel.Interrupt, 1'b0));
		blocks.push_back(to_block(regmodel.Buffer_IRQs, 1'b0));
		blocks.push_back(to_block(regmodel.SPI_CMD_STAT, 1'b0));
		blocks.push_back(to_block(regmodel.SPI, 1'b0));
		blocks.push_back(to_block(regmodel.Timebase, 1'b1)); // CLKREF_CONF will cause HE (hardware error)
		blocks.push_back(to_block(regmodel.Supply, 1'b1));  // LDO UV will cause DSI UV cause PKG_STAT != 0!
		
		check_all(blocks);
	endtask
	
	function automatic reg_block_definition to_block(uvm_reg_block block, bit causes_hardware_error);
		reg_block_definition definition;
		definition.block = block;
		definition.causes_hardware_error = causes_hardware_error;
		return definition;
	endfunction
	
	task check_all(reg_block_definition blocks[$]);
		log_sim_description($sformatf("running UVM register sequences for %0d blocks", blocks.size()), LOG_LEVEL_SEQUENCE);
		
		// !!! check resets before accessing registers
		foreach(blocks[i]) begin
			check_hdl_paths(blocks[i].block);
			check_hw_reset(blocks[i].block);
		end
		foreach(blocks[i]) begin
			if(blocks[i].causes_hardware_error) begin
				// disable automatic check for HE flag
				get_checker_config().enable_hardware_error_check = 1'b0;
			end
			check_reg_access(blocks[i].block);
			check_reg_bit_bash(blocks[i].block);
			get_checker_config().enable_hardware_error_check = 1'b1;
		end
	endtask
	
	task check_hdl_paths(uvm_reg_block block);
		uvm_reg_mem_hdl_paths_seq hdl_paths_seq;
		log_sim_description($sformatf("check HDL paths for block %s", block.get_name()), LOG_LEVEL_SEQUENCE);
		
		hdl_paths_seq = uvm_reg_mem_hdl_paths_seq::type_id::create("hdl_paths_seq");
		hdl_paths_seq.model = block;
		`uvm_send(hdl_paths_seq); 
		#10us;
	endtask	
	
	task check_hw_reset(uvm_reg_block block);
		uvm_reg_hw_reset_seq hw_reset_seq;
		log_sim_description($sformatf("check hardware resets for block %s", block.get_name()), LOG_LEVEL_SEQUENCE);
		
		hw_reset_seq = uvm_reg_hw_reset_seq::type_id::create("hw_reset_seq");
		hw_reset_seq.model = block;
		`uvm_send(hw_reset_seq); 	
		#10us;
	endtask
	
	task check_reg_access(uvm_reg_block block);
		uvm_reg_access_seq reg_access_seq;
		log_sim_description($sformatf("check register access for block %s", block.get_name()), LOG_LEVEL_SEQUENCE);
		
		reg_access_seq = uvm_reg_access_seq::type_id::create("reg_access_seq");
		reg_access_seq.model = block;
		`uvm_send(reg_access_seq);
		#10us;
	endtask	
		
	task check_reg_bit_bash(uvm_reg_block block);
		uvm_reg_bit_bash_seq reg_bit_bash_seq;
		log_sim_description($sformatf("check bit bashing for block %s", block.get_name()), LOG_LEVEL_SEQUENCE);
		
		reg_bit_bash_seq = uvm_reg_bit_bash_seq::type_id::create("reg_bit_bash_seq");
		reg_bit_bash_seq.model = block;
		`uvm_send(reg_bit_bash_seq);
		#10us;
	endtask	
	
endclass
