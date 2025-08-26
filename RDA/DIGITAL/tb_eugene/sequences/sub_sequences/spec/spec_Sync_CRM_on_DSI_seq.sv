typedef enum {
    unsynchronized = 0,
    synchronized = 1,
    wait_before_broadcast = 2
} sync_set_t;

class spec_Sync_CRM_on_DSI_seq extends base_dsi_master_seq;

	`uvm_object_utils(spec_Sync_CRM_on_DSI_seq)

    rand sync_set_t sync_set;
    
	function new(string name = "");
		super.new("spec_Sync_CRM_on_DSI_seq");
	endfunction : new

	virtual task run_tests();
        spi_read_crm_data_packets_seq read_seq;
        dsi3_crm_packet packets[$];
        
        case (sync_set)
    	   	synchronized: 			log_sim_description("CRM Commands synchronized on DSI3 Channels", LOG_LEVEL_SEQUENCE);
    	   	wait_before_broadcast: 	log_sim_description("CRM Commands synchronized on DSI3 Channels, wait before broadcast command", LOG_LEVEL_SEQUENCE);
			default:  				log_sim_description("CRM Commands unsynchronized on DSI3 Channels", LOG_LEVEL_SEQUENCE);
		endcase
      
       	create_valid_CRM_packets_with_data(packets, 2'b10);
       	create_CRM_packets_without_data(2, 2'b10);
		create_CRM_packets_without_data(3, 2'b01);
        
        fork
            begin
                `spi_frame_begin
	                `spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 0;)
	                `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
	                `spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1;)
	            	if(sync_set == synchronized) begin
	                    `spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 0; channel_bits==2'b11;)
	            	end
	                else if (sync_set == wait_before_broadcast) begin
	                    `spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 0; channel_bits==2'b11;)
	                    `spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 100;)
	                end
	                `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                `spi_frame_end
            end
                
            begin
                #500us;
                `spi_frame_begin
                `spi_frame_send(read_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
                `spi_frame_end
                #1us;
            end
        join
        
		read_seq.expect_flags( 2'd1, packets[0].crc_correct ? {} : {CRC});
		read_seq.expect_packet(2'd1, packets[0]);
        #1ms;
	endtask
endclass
