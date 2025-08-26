/**
 * Interface: elip_full_if
 * 
 * ELIP Interface
 */
interface elip_full_if;
	
	import project_pkg::*;
	
	// @SuppressProblem -nowarnmiss 1 -type fully_unread_static_variable -count 1 -length 1 -hierarchy "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.elip_spi_read"
	logic		wr;
	// @SuppressProblem -nowarnmiss 1 -type fully_unread_static_variable -count 1 -length 1 -hierarchy "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.elip_write_register"
	logic		rd;
	// @SuppressProblem -nowarnmiss 1 -type partially_unread_data -count 1 -length 1 -hierarchy "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_data_storage.elip_ram"
	elip_addr_t	addr;
	// @SuppressProblem -nowarnmiss 1 -type fully_unread_static_variable -count 1 -length 1 -hierarchy "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.elip_spi_read"
	// @SuppressProblem -nowarnmiss 1 -type partially_unread_data -count 1 -length 1 -hierarchy "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.i_data_storage.elip_2_registers"
	data_ecc_t	data_write;
	// @SuppressProblem -nowarnmiss 1 -type fully_unread_static_variable -count 1 -length 1 -hierarchy "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.elip_main_fsm","top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.elip_write_register"
	// @SuppressProblem -nowarnmiss 1 -type partially_unread_data -count 1 -length 1 -hierarchy "top_tb.th.i_dut_wrapper.xtop.xdigtop.i_logic_top.elip_jtag"
	data_ecc_t	data_read;
	logic		ready;
	
	modport master (
		output	wr, rd, addr, data_write,
		input	data_read, ready
	);
	
	modport slave (
		input	wr, rd, addr, data_write,
		output	data_read, ready
	);
	
endinterface
