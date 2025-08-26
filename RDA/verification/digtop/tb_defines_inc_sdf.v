
`ifdef EASIER_UVM_TB
	`define ASIC_TB_INST $root.top_tb.th.i_dut_wrapper
	`ifdef  target_technology_FPGA
		`define ASIC_INST          `ASIC_TB_INST.fpga_inst
	`else
		`define ASIC_INST          `ASIC_TB_INST.asic_inst
	`endif
`else
	`ifdef  target_technology_FPGA
		`define ASIC_TB_INST       $root.fpga_tb
		`define ASIC_INST          `ASIC_TB_INST.fpga_inst
	`else
		`define ASIC_TB_INST       $root.asic_tb
		`define ASIC_INST          `ASIC_TB_INST.asic_inst
	`endif
`endif

//define DIGITAL_INST         `ASIC_INST.digital_inst
`define DIGITAL_INST         snps_sptop.xdut.xdigital

`define ACM0_CORE_SYS_INST     `DIGITAL_INST.core_iomux_inst.core_inst_cpu_core_sys_inst
`define ACM_TESTER_SHELL_INST  `ASIC_TB_INST.acm_core_sys_tester_shell_inst
`define SIMIO_TESTER_INST      `ACM_TESTER_SHELL_INST.simio_tester_inst

`include "acm0_core_sys_paths_inc.v"

