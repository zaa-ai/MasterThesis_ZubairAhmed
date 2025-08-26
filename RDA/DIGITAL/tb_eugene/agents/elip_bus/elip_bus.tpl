agent_name = elip_bus
trans_item = elip_tr

# transaction variables
trans_var = rand logic[15:0]	address; 
trans_var =      logic[15:0]	data_read;
trans_var =      logic[5:0]     data_read_ecc;
trans_var = rand logic[15:0]	data_write;
trans_var = rand logic[5:0]     data_write_ecc;
trans_var = rand bit			write;

# constraints

if_port  = parameter address_width = 16;
if_port  = parameter data_width = 16;
if_port  = parameter ecc_width = 6;
if_port  = logic ready;
if_port  = logic write;
if_port  = logic read;
if_port  = logic[data_width-1:0] data_read;
if_port  = logic[data_width-1:0] data_write;
if_port  = logic[ecc_width-1:0]  data_read_ecc;
if_port  = logic[ecc_width-1:0]  data_write_ecc;
if_port  = logic[address_width-1:0] address;
if_port  = logic clk;
if_port  = logic rstn;

# config object values

driver_inc_inside_class = includes/elip_driver_inc_inside_class.sv
monitor_inc				= includes/elip_monitor_inc.sv
agent_seq_inc           = includes/elip_seq_inc.sv
