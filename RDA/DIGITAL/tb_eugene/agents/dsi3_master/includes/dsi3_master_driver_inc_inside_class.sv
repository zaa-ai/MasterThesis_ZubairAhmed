task run_phase(uvm_phase phase);
	// initialize DSI3 interface
	forever
	begin
		seq_item_port.get_next_item(req);
		do_drive();
		seq_item_port.item_done(rsp);
	end
endtask : run_phase

task do_drive ();
	// nothing to drive here, this agent is passive
endtask : do_drive
