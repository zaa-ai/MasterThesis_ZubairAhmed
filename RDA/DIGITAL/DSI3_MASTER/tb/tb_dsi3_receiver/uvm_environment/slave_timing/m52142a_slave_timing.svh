class m52142a_slave_timing extends dsi3_slave_pkg::slave_timing_container#(.kramp(4), .data_sets(64));
	
	function new();
		super.new();
		foreach (slave_timing[i,j]) begin
			`include "slave_timing/slave_timing_kramp0.sv"
			`include "slave_timing/slave_timing_kramp1.sv"
			`include "slave_timing/slave_timing_kramp2.sv"
			`include "slave_timing/slave_timing_kramp3.sv"
		end
	endfunction
	
endclass