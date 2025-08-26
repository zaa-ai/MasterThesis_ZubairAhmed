task run_phase(uvm_phase phase);
	vif.data_write = '0;
	vif.data_write_ecc = '0;
	vif.address = '0;
	vif.read = 1'b0;
	vif.write = 1'b0;

	forever	begin
		seq_item_port.get_next_item(req);
		do_drive();
		seq_item_port.item_done(rsp);
	end
endtask : run_phase

task do_drive ();
	@(posedge vif.clk);
	if (req.write)	begin
		vif.data_write = req.data_write;
		vif.data_write_ecc = req.data_write_ecc;
	end
	vif.address = req.address;
	vif.read = ~req.write;
	vif.write = req.write;
	@(negedge vif.clk);
	if (vif.ready ==  1'b0) begin
		@(posedge vif.ready);
	end
	@(posedge vif.clk);
	req.data_read = vif.data_read;
	req.data_read_ecc = vif.data_read_ecc;
	vif.write = 1'b0;
	vif.read = 1'b0;
endtask : do_drive
