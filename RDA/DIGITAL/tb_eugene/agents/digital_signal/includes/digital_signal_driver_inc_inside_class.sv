task run_phase(uvm_phase phase);
	`uvm_info(get_type_name(), "run_phase", UVM_HIGH)
	// initialize if
	vif.D = m_config.initial_value;
	forever begin
		seq_item_port.get_next_item(req);
		`uvm_info(get_name(), {"req item\n",req.sprint}, UVM_HIGH)
		do_drive();
		seq_item_port.item_done(rsp);
	end
endtask : run_phase

task do_drive();
	// set pin
	vif.D = req.value;
endtask : do_drive
