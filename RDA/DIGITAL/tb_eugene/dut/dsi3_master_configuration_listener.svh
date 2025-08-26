/**
 * Class: dsi3_master_configuration_listener
 * 
 * UVM component, which listens to SPI and RESB transactions and updates the DSI3 master bit times accordingly.
 */
class dsi3_master_configuration_listener extends uvm_subscriber #(spi_command_frame_seq);
	
	`uvm_component_utils(dsi3_master_configuration_listener)
	
	uvm_analysis_imp_resb #(digital_signal_tr, dsi3_master_configuration_listener) resb_export;
	uvm_analysis_port #(dsi3_master_configuration_tr) configuration_port;

	ral_sys_device_registers		regmodel;
	dsi3_master_configuration_tr	configuration;
	
	function new(string name = "dsi3_master_configuration_listener", uvm_component parent);
		super.new(name, parent);
		resb_export = new("resb_export", this);
		configuration_port = new("configuration_port", this);
	endfunction
	
	virtual function void start_of_simulation_phase(uvm_phase phase);
		configuration = default_transaction();
		configuration_port.write(configuration);
	endfunction	
	
	// reset (RESB pin)
	function void write_resb(digital_signal_tr t);
		configuration = default_transaction();
		configuration_port.write(configuration);
	endfunction
	
	/**
	 * Create a initial default configuration from register reset values.
	 */
	function dsi3_master_configuration_tr default_transaction();
		ral_reg_common_DSI3_block_registers_DSI_ENABLE DSI_ENABLE			= regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE;
		ral_reg_common_DSI3_block_registers_DSI_CFG	DSI_CFG 				= regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG;
		ral_reg_common_DSI3_block_registers_DSI_TX_SHIFT DSI_TX_SHIFT 		= regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT;
		ral_reg_common_DSI3_block_registers_CRM_TIME CRM_TIME 				= regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME;
		ral_reg_common_DSI3_block_registers_CRM_TIME_NR CRM_TIME_NR			= regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR;
		
		dsi3_master_configuration_tr default_config = dsi3_master_configuration_tr::create_transaction();
		default_config.dsi_enable  	= 2'(DSI_ENABLE.TRE.get_reset());
		default_config.bit_time 	= dsi3_pkg::dsi3_bit_time_e'(DSI_CFG.BITTIME.get_reset());
		default_config.chip_time 	= int'(DSI_CFG.CHIPTIME.get_reset()) + 2;
		default_config.crc_en 		= bit'(DSI_CFG.CRC_EN.get_reset());
		default_config.sync_pdcm 	= bit'(DSI_CFG.SYNC_PDCM.get_reset());
		default_config.sync_master 	= bit'(DSI_CFG.SYNC_MASTER.get_reset());
		default_config.crm_time 	= int'(CRM_TIME.TIME.get_reset());
		default_config.crm_time_nr 	= int'(CRM_TIME_NR.TIME.get_reset());
		
		// default TX shift value
		default_config.tx_shift_value = int'(DSI_TX_SHIFT.SHIFT.get_reset());
		return default_config;
	endfunction
	
	virtual function void write(spi_command_frame_seq t);
		spi_tx_crc_request_seq crc_seq;
		if($cast(crc_seq, t.commands[$]) == 1) begin
			if(crc_seq.mosi_crc_correct == 1'b1) begin
				foreach(t.commands[i]) begin
					spi_write_master_register_seq write_seq;
					if($cast(write_seq, t.commands[i]) == 1) begin
						handle_spi_write_master_register(write_seq);
					end
				end
			end
		end
	endfunction
	
	function void handle_spi_write_master_register(spi_write_master_register_seq t);
		uvm_reg_map	reg_map = regmodel.get_default_map();
		uvm_reg	reg_addressed= reg_map.get_reg_by_offset(t.address, 1);
		
		if (reg_addressed != null) begin
			ral_reg_common_DSI3_block_registers_DSI_ENABLE dsi_enable 			= regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE;
			ral_reg_common_DSI3_block_registers_DSI_CFG	dsi_cfg 				= regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG;
			ral_reg_common_DSI3_block_registers_DSI_TX_SHIFT dsi_tx_shift 		= regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT;
			ral_reg_common_DSI3_block_registers_CRM_TIME dsi_crm_time 			= regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME;
			ral_reg_common_DSI3_block_registers_CRM_TIME_NR dsi_crm_time_nr		= regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR;
			
			// DSI_ENABLE
			if (reg_addressed == dsi_enable) begin
				configuration.dsi_enable = 2'(value_from_field(dsi_enable.TRE, t.data));
				configuration_port.write(configuration);
			end
			// DSI_CFG
			else if (reg_addressed == dsi_cfg) begin
				configuration.bit_time 		= dsi3_pkg::dsi3_bit_time_e'(value_from_field(dsi_cfg.BITTIME, t.data));
				configuration.chip_time 	= value_from_field(dsi_cfg.CHIPTIME, t.data) + 2;
				configuration.crc_en		= bit'(value_from_field(dsi_cfg.CRC_EN, t.data));
				configuration.sync_pdcm 	= bit'(value_from_field(dsi_cfg.SYNC_PDCM, t.data));
				configuration.sync_master 	= bit'(value_from_field(dsi_cfg.SYNC_MASTER, t.data));
				configuration_port.write(configuration);
			end
			// TX_SHIFT
			else if (reg_addressed == dsi_tx_shift) begin
				int tx_shift = value_from_field(dsi_tx_shift.SHIFT, t.data);
				configuration.tx_shift_value = tx_shift;
				configuration_port.write(configuration);
			end
			// CRM_TIME
			else if (reg_addressed == dsi_crm_time) begin
				int crm_time = value_from_field(dsi_crm_time.TIME, t.data);
				configuration.crm_time = crm_time;
				configuration_port.write(configuration);
			end
			// CRM_TIME_NR
			else if (reg_addressed == dsi_crm_time_nr) begin
				int crm_time_nr = value_from_field(dsi_crm_time_nr.TIME, t.data);
				configuration.crm_time_nr = crm_time_nr;
				configuration_port.write(configuration);
			end
		end
	endfunction
	
	function int value_from_field(uvm_reg_field field, logic[15:0] data);
		int lsb = field.get_lsb_pos();
		int size = field.get_n_bits();
		return (data >> lsb) & ((2**size) - 1);
	endfunction
endclass
