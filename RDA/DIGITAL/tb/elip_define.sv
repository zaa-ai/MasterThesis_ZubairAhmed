elip_if #(.addr_width(ADDR_WIDTH), .data_width(DATA_WIDTH)) elip_vif(); 
l16				o_elip_out; 
task elip_read(input elip_addr_t addr, output elip_data_t elip_data_out); 
	@(negedge clk_rst.clk); 
	elip_vif.rd = 1'b1; 
	elip_vif.addr = addr;
	#10ns;
	elip_data_out = o_elip_out;
	@(posedge clk_rst.clk);
	#1ns;
	
	#5ns;
	elip_idle(); 
endtask 
task elip_write(input elip_addr_t addr, elip_data_t data); 
	@(negedge clk_rst.clk); 
	elip_vif.wr = 1'b1; 
	elip_vif.addr = addr; 
	elip_vif.data_write = data; 
	@(posedge clk_rst.clk);
	#5ns;
	elip_idle();
endtask 
task elip_idle(); 
	elip_vif.rd = 1'b0; 
	elip_vif.wr = 1'b0;
	elip_vif.addr = '0;
	elip_vif.data_write = '0;
endtask

initial begin
	elip_idle();
end

task check_elip(elip_addr_t addr, elip_data_t data);
	l16 elip_data_out;
	elip_read(addr, elip_data_out);
	`FAIL_UNLESS_EQUAL (elip_data_out, data)
endtask
