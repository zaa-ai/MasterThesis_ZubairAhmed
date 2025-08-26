agent_name = jtag_master
trans_item = jtag_tr

# transaction variables
trans_var = rand byte unsigned	ir_length; 
trans_var = rand int unsigned	dr_length;
trans_var = rand int unsigned	ir_value;
trans_var = rand logic[265:0] 	dr_value;
trans_var = rand bit 			init_jtag;
trans_var = logic[265:0]		read_dr;
trans_var = int	unsigned		read_ir;

# constraints
trans_var = constraint ir_length_co{ ir_length >= 0;}
trans_var = constraint ir_value_order_co{ solve ir_length before ir_value;}
trans_var = constraint ir_value_co{ ir_value inside { [0:(2**(ir_length+1))-1] };}

trans_var = constraint dr_order_co{solve ir_value before dr_length;}
trans_var = constraint dr_length_co{dr_length inside {[0:65535]};}
trans_var = constraint dr_value_order_co{ solve dr_length before dr_value;}
trans_var = constraint dr_value_co{dr_value inside{ [0:(2**(dr_length+1))-1]};}

if_port  = logic TRST;
if_port  = logic TCK;
if_port  = logic TDI;
if_port  = logic TMS;
if_port  = wire TDO;

# config object values
config_var = time cycle_time 			= 666ns;
config_var = logic leading_level 		= 1'b1;

config_var = bit[7:0] ir_length			= 8'd8;
config_var = int dr_length 				= 32;
config_var = int dr_length_elip_data	= 16;
config_var = int dr_length_elip_addr	= 16;

uvm_seqr_class = yes
trans_generate_methods_inside_class = no
trans_inc_inside_class 	 = includes/jtag_trans_inc_inside_class.svh
driver_inc_inside_class  = includes/jtag_driver_inc_inside_class.sv
agent_seq_inc 			 = includes/jtag_seq_inc.sv
agent_inc_inside_package = includes/jtag_agent_inc_inside_package.svh
