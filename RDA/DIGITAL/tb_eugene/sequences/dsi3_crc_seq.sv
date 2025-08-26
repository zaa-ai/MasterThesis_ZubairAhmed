class dsi3_crc_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_crc_seq)

	function new(string name = "");
		super.new("dsi3_crc_seq");
		log_task_name = 1'b0;
	endfunction
	
	virtual task run_tests();
		get_checker_config().enable_check_pdcm_period = 1'b1;

        log_sim_task("DSI3 CRC calculation - PDCM 8bit - SEED xFF");
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels == 2'b11; source_id == dsi3_pkg::SID_0Bit;)
        log_sim_measure ("seed_FF", "", "", "PASS");
        log_sim_status("PASS");
        log_sim_task("DSI3 CRC calculation - PDCM 8bit - SEED 4bit");
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels == 2'b11; source_id == dsi3_pkg::SID_4Bit;)
        log_sim_measure ("seed_SID_4Bit", "", "", "PASS");
        log_sim_status("PASS");
        log_sim_task("DSI3 CRC calculation - PDCM 8bit - 8bit SEED");
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels == 2'b11; source_id == dsi3_pkg::SID_8Bit;)
        log_sim_measure ("seed_SID_8Bit", "", "", "PASS");
        log_sim_status("PASS");
        log_sim_task("DSI3 CRC calculation - PDCM 16bit");
		`create_and_send_with(random_pdcm_and_read_data_seq, active_channels == 2'b11; source_id == dsi3_pkg::SID_16Bit_CRC;)
        log_sim_measure ("seed_FFFF", "", "", "PASS");
        log_sim_status("PASS");
        
        log_sim_task("DSI3 CRC calculation - CRM 8bit CRC");
        `create_and_send_with(crm_random_on_different_channels_seq, )
        log_sim_measure ("seed_FF", "", "", "PASS");
        log_sim_status("PASS");
	endtask
endclass
