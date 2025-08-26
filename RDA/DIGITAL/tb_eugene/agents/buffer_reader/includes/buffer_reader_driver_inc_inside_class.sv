
virtual clk_reset_if vif_clk_rst;

task run_phase(uvm_phase phase);
	initialize();
	forever	begin
		seq_item_port.get_next_item(req);
		do_drive();
		seq_item_port.item_done(rsp);
	end
endtask : run_phase

task do_drive();
	if (vif_clk_rst.clk == 1'b0) begin
		@(posedge vif_clk_rst.clk);
		#1;
	end
	vif.action = req.action;
	if (req.action == BUFFER_MOVE_POINTER) vif.step = req.data[5:0];
	
	check_ready();
	req.empty = vif.empty;
	req.data = vif.data.data;
	req.ecc  = vif.data.ecc;
	@(posedge vif_clk_rst.clk);
	initialize();
endtask : do_drive

task check_ready();
	do begin
		@(negedge vif_clk_rst.clk);
		#5ns;
	end while (vif.ready == 1'b0);
endtask

task initialize();
	vif.action = IDLE_READ;
	vif.step = '0;
endtask
