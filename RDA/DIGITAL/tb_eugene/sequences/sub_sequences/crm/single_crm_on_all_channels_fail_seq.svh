class single_crm_on_all_channels_all_fail_seq#(int sub_test_level=1) extends single_crm_on_all_channels_seq;
	
	`uvm_object_param_utils(single_crm_on_all_channels_all_fail_seq)

	function new(string name = "");
		super.new("single_crm_on_all_channels_all_fail");
        set_name("single_crm_on_all_channels_all_fail");
		received_data = 1'b0;
	endfunction
	
	virtual function void check_data(spi_read_crm_data_packets_seq read, dsi3_crm_packet packets[$]);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read.expect_empty(2'(channel));
		end
	endfunction
	
endclass


