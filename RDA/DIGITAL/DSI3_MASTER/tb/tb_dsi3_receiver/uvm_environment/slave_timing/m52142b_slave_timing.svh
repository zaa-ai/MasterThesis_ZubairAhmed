class m52142b_slave_timing extends dsi3_slave_pkg::slave_timing_container#(.kramp(4), .data_sets(256));
	
	function new();
		super.new();
		foreach (slave_timing[i,j]) begin
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k0_slave_timing.sv"
			
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k1_slave_timing.sv"
			
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k2_slave_timing.sv"
			
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k3_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k3_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k3_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k3_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k3_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k3_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k3_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k3_slave_timing.sv"
		end
	endfunction
	
endclass

class m52142b_slave_timing_k0 extends dsi3_slave_pkg::slave_timing_container#(.kramp(1), .data_sets(256));
	function new();
		super.new();
		foreach (slave_timing[i,j]) begin
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k0_slave_timing.sv"
		end
	endfunction
	
endclass

//class m52142b_slave_timing_k1 extends dsi3_slave_pkg::slave_timing_container#(.kramp(1), .data_sets(256));
//	function new();
//		super.new();
//		foreach (slave_timing[i,j]) begin
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k1_slave_timing.sv"
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k1_slave_timing.sv"
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k1_slave_timing.sv"
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k1_slave_timing.sv"
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k1_slave_timing.sv"
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k1_slave_timing.sv"
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k1_slave_timing.sv"
//			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k1_slave_timing.sv"
//		end
//	endfunction
//	
//endclass

class m52142b_slave_timing_k012 extends dsi3_slave_pkg::slave_timing_container#(.kramp(3), .data_sets(256));
	function new();
		super.new();
		foreach (slave_timing[i,j]) begin
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k0_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k0_slave_timing.sv"
			
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k1_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k1_slave_timing.sv"
			
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ff_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_fs_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_sf_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmax_ss_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ff_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_fs_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_sf_k2_slave_timing.sv"
			`include "slave_timing/TOP_MIXED_appl_dsi_slavemodel_tmin_ss_k2_slave_timing.sv"
		end
	endfunction
	
endclass
