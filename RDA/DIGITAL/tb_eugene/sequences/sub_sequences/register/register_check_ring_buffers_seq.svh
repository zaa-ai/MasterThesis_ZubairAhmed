class register_check_ring_buffers_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_check_ring_buffers_seq)
	
	function new(string name = "");
		super.new("register_check_ring_buffers");
	endfunction : new
	
	/**
	 * Check reset value of all ring buffer registers: SPI-Cmd, 2x DSI-Cmd, 2x DSI-Data
	 * - BUF_FREE
	 * - BUF_READ_POINTER
	 * - BUF_WRITE_POINTER
	 * - BUF_VALID_POINTER
	 */
	virtual task run_tests();
		log_sim_description("check ring buffer register reset values", LOG_LEVEL_SEQUENCE);
		
		check_ring_buffer_register_resets(regmodel.SPI_CMD_STAT, project_pkg::SIZE_SPI_CMD_BUF-1, project_pkg::BASE_ADDR_SPI_CMD_BUF);
			
		check_ring_buffer_register_resets(regmodel.DSI_CMD_STAT[0], project_pkg::SIZE_DSI_CMD_BUF-1, project_pkg::BASE_ADDR_DSI_CMD_BUF[0]);
		check_ring_buffer_register_resets(regmodel.DSI_CMD_STAT[1], project_pkg::SIZE_DSI_CMD_BUF-1, project_pkg::BASE_ADDR_DSI_CMD_BUF[1]);
			
		check_ring_buffer_register_resets(regmodel.DSI_PDCM_STAT[0], project_pkg::SIZE_DSI_PDCM_BUF-1, project_pkg::BASE_ADDR_DSI_PDCM_BUF[0]);
		check_ring_buffer_register_resets(regmodel.DSI_PDCM_STAT[1], project_pkg::SIZE_DSI_PDCM_BUF-1, project_pkg::BASE_ADDR_DSI_PDCM_BUF[1]);
		check_ring_buffer_register_resets(regmodel.DSI_CRM_STAT[0],  project_pkg::SIZE_DSI_CRM_BUF-1, project_pkg::BASE_ADDR_DSI_CRM_BUF[0]);
		check_ring_buffer_register_resets(regmodel.DSI_CRM_STAT[1],  project_pkg::SIZE_DSI_CRM_BUF-1, project_pkg::BASE_ADDR_DSI_CRM_BUF[1]);
		
	endtask
	
	task check_ring_buffer_register_resets(ral_block_buf_ctrl block, logic[15:0] size, logic[15:0] ram_address);
		uvm_reg_data_t value;
		
		block.ring_buffer_registers.BUF_FREE.read(status, value);
		if(value != 64'(size)) `uvm_error(this.get_name(), $sformatf("Unexpected BUF_FREE value in ring buffer %s, expected %0h, got %0h.", block.get_name(), size, value))
		
		block.ring_buffer_registers.BUF_READ_POINTER.read(status, value);
		if(value != 64'(ram_address)) `uvm_error(this.get_name(), $sformatf("Unexpected BUF_READ_POINTER value in ring buffer %s, expected %0h, got %0h.", block.get_name(), ram_address, value))
		
		block.ring_buffer_registers.BUF_WRITE_POINTER.read(status, value);
		if(value != 64'(ram_address)) `uvm_error(this.get_name(), $sformatf("Unexpected BUF_WRITE_POINTER value in ring buffer %s, expected %0h, got %0h.", block.get_name(), ram_address, value))

		block.ring_buffer_registers.BUF_VALID_POINTER.read(status, value);
		if(value != 64'(ram_address)) `uvm_error(this.get_name(), $sformatf("Unexpected BUF_VALID_POINTER value in ring buffer %s, expected %0h, got %0h.", block.get_name(), ram_address, value))
	endtask
endclass