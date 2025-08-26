dut_top 		= TOP_WRAPPER				# Module Name of DUT
dut_iname 		= i_dut_wrapper				# Instance name of generated DUT module. 

common_pkg 		= common_pkg.sv        		# Include package file from dut directory
common_env_pkg	= common_env_pkg.svh		# Include package file from inc directory

file_header_inc = file_header.txt

top_seq_inc 	= includes/top_seq_inc.sv

test_prepend_to_build_phase = includes/test_prepend_to_build_phase.sv
test_inc_before_class = includes/test_inc_before_class.sv
test_inc_inside_class = includes/test_inc_inside_class.sv
tb_inc_before_run_test = includes/tb_inc_before_run_test.sv

# func register model
regmodel_name 		= regmodel
regmodel_pkg  		= regmodel_pkg
top_reg_block_type 	= ral_sys_device_registers

# test register model
regmodel_name 		= test_regmodel
regmodel_pkg  		= test_regmodel_pkg
top_reg_block_type 	= ral_sys_jtag_test_registers

top_env_config_inc_before_class = includes/top_env_config_inc_before_class.sv
top_env_inc_before_class      	= includes/top_env_inc_before_class.sv        
top_env_append_to_build_phase 	= includes/top_env_append_to_build_phase.sv   
top_env_inc_inside_class 	  	= includes/top_env_inc_inside_class.sv 	 	 
top_env_append_to_connect_phase = includes/top_env_append_to_connect_phase.sv 

#to remove topology and factory override been printed
top_env_generate_end_of_elaboration = no