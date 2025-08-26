class single_pdcm_on_all_channels_fail_seq extends single_pdcm_on_all_channels_seq;
    
	`uvm_object_utils(single_pdcm_on_all_channels_fail_seq)
	
	function new(string name = "");
		super.new("single_pdcm_on_all_channels_fail");
        set_name("single_pdcm_on_all_channels_fail");
        received_data = 1'b0;
	endfunction : new
	
    virtual task check_data(spi_read_pdcm_frame_seq read_seq, tdma_scheme_pdcm schemes[project_pkg::DSI_CHANNELS-1:0]);
        for (int selected_channel=0; selected_channel < project_pkg::DSI_CHANNELS; selected_channel++) begin
            read_seq.expect_empty(2'(selected_channel), 0);
        end
    endtask
	
endclass
