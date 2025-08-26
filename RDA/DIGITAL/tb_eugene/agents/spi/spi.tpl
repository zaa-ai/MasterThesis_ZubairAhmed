agent_name = spi
trans_item = spi_tr

# transaction variables
trans_enum_var = rand spi_tr_type tr_type;
trans_var      = rand logic[15:0] data_in;
trans_var      = logic[15:0] data_out;
trans_var      = int word_index;
trans_var      = int bit_count;

# constraints

if_port  = logic SCK;
if_port  = logic SDI;
if_port  = logic SDO;
if_port  = logic CSN;

# config object values
config_var = time cycle_time 				= 1000ns;	// Bit time
config_var = bit csn_polarity				= 1'b0; 	// 0: active low					1: active high
config_var = bit sck_polarity				= 1'b0; 	// 0: inactive low					1: inactive high 
config_var = bit sck_phase					= 1'b1; 	// 0: first sample then shift		1: first shift then sample
config_var = logic sck_init_value			= 1'b0; 	// intial value of sck
config_var = time csn_to_sck				= 1000ns;	// Time from activation of CSN to first SCK edge
config_var = time sck_to_csn				= 1000ns;	// Time from last SCK edge to deactivation of CSN
config_var = time inter_word_gap			= 0us;      // Time between 2 successive SPI words
config_var = spi_csb_handler csb_handler	= per_word_csb_hander::create();

uvm_seqr_class = yes

trans_generate_methods_inside_class = no
agent_cover_generate_methods_inside_class = no

trans_inc_before_class 		= includes/spi_trans_inc_before_class.svh
trans_inc_inside_class  	= includes/spi_trans_inc_inside_class.svh
driver_inc_inside_class 	= includes/spi_driver_inc_inside_class.sv   
agent_inc_inside_package 	= includes/spi_agent_inc_inside_package.svh

monitor_inc				 	= includes/spi_monitor_inc.sv 				
agent_seq_inc           	= includes/spi_seq_inc.sv