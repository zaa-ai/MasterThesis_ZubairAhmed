
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
	vif.data.data = req.data;
	vif.data.ecc = req.ecc;
	
	@(negedge vif_clk_rst.clk);
	if (vif.ready == 1'b0) begin
		@(posedge vif.ready);
	end
	req.full = vif.full;
	req.nearly_full = vif.nearly_full;
	@(posedge vif_clk_rst.clk);
	initialize();
endtask
	
task initialize();
	vif.action = PDCM_IDLE_WRITE;
	vif.data.data = '0;
	vif.data.ecc = DWF_ecc_gen_chkbits(16, 6, 0);
endtask
