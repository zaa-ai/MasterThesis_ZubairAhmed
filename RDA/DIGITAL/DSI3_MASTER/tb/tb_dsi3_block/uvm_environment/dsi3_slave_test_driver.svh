/**
 * Class: dsi3_slave_test_driver
 * 
 * DSI3 slave driver with additional capability to send symbols
 */
class dsi3_slave_test_driver extends dsi3_slave_driver;
	`uvm_component_utils(dsi3_slave_test_driver)
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	task send_test_symbol(input dsi3_pkg::dsi3_symbol symbol, input slave_rxd_timing rxd_timing);
		send_symbol(symbol, rxd_timing, 1'b0);
	endtask
	
endclass

