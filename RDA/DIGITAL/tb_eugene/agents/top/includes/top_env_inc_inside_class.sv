dsi3_master_transmission_checker m_master_transmission_checker[$];
dsi3_transaction_recorder m_transaction_recorder;
tdma_scheme_upload_listener m_tdma_scheme_upload_listener;
dsi3_master_configuration_listener m_dsi3_configuration_listener;

spi_protocol_listener spi_listener;
behaviour_checker m_behaviour_checker;

register_resetter test_register_resetter;
edf_parameter_model edf_parameters;

function void set_frontdoor_for_block(uvm_reg_block block, uvm_reg_frontdoor frontdoor);
	uvm_reg	registers[$];
	block.get_registers(registers);
	for(int i=0; i<registers.size(); i++) begin
		uvm_reg next_reg = registers[i];
		next_reg.set_frontdoor(frontdoor);
	end	
endfunction

function void set_frontdoor(uvm_reg_block regmodel, uvm_reg_frontdoor frontdoor, uvm_sequencer_base sequencer, string top_hdl_path);
	uvm_reg_block blocks[$];
	  
	frontdoor.sequencer = sequencer;
	
	// lock (this statement is missing in Easier UVM Generator)
	regmodel.set_coverage(UVM_CVR_ALL); // turn ff coverage
	regmodel.get_default_map().set_auto_predict(1);
	regmodel.lock_model();
	regmodel.reset();
			
	regmodel.get_blocks(blocks, UVM_NO_HIER);
	foreach (blocks[i]) begin
		set_frontdoor_for_block(blocks[i], frontdoor);
	end
	regmodel.add_hdl_path(top_hdl_path);
	
endfunction
