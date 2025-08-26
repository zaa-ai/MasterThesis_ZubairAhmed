/*------------------------------------------------------------------------------
 * File          : dsi3_data_writer.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Feb 28, 2023
 * Description   : Module for writing received data to buffer
 *------------------------------------------------------------------------------*/
module dsi3_pdcm_data_writer import project_pkg::*; import dsi3_pkg::*; import buffer_if_pkg::*;  (
        clk_reset_if.slave	                clk_rst,
        timebase_info_if.slave				time_base,
        DSI3_channel_registers_PACKET_STAT_if.slave	DSI3_channel_registers_PACKET_STAT,
        DSI3_channel_registers_FRAME_STAT_if.slave	DSI3_channel_registers_FRAME_STAT,
        pdcm_buffer_writer_if.master		pdcm_data_writer,
        dsi3_common_config_if.dsi3_block	common_config,
        general_data_writer_inputs_if.slave    general_inputs,
        tdma_reader_if.master               tdma_reader,
        
        input   logic                       i_enable,
        input	logic				        i_clear_flag_for_received_packets,
        input   logic                       i_clear_data_buffer,
        input   logic                       i_clear_and_invalidate_data_buffer,
        input   logic                       i_receive_time_out_tick,
        input   logic                       i_stop,
        output	logic				        o_received_at_least_one_packet,
        output	logic				        o_hw_fail_data_fsm
);
    
    import  tdma_pkg::*;
    import  spi_implementation_pkg::*;
    
    /*###   ECC_ENCODER - data path to SPI  ####################################*/
    data_t	dsi_data_writer;
    ecc_t	dsi_data_writer_ecc;
    logic   recalculate_ecc;
    
    assign pdcm_data_writer.data.data = dsi_data_writer;
    assign pdcm_data_writer.data.ecc  = (recalculate_ecc) ? dsi_data_writer_ecc : general_inputs.rx_data.ecc; 
    
    ecc_encoder #(
        .DATA_WIDTH  (DATA_WIDTH),
        .ECC_WIDTH   (ECC_WIDTH)
    ) i_ecc_enc_dsi3_rec (
        .i_data      (dsi_data_writer),
        .o_ecc       (dsi_data_writer_ecc)
    );
    
    /*#########################################################################*/
    logic   reset_frame_info;
    
    typedef logic[7:0]  packet_counter_t;
    // counting packets in the frame, maybe less or more than specified in TDMA
    packet_counter_t    packet_counter, packet_counter_next;
    // representing current position in TDMA scheme
    packet_counter_t    packet_index, packet_index_next;
    packet_counter_t    tdma_header_packet_count;
    
    logic	ce_flag, ce_flag_next, ve_flag, ve_flag_next;
    logic	mask_ce_ve_flag_setting, mask_ce_ve_flag_setting_next;
    logic	reset_ce_ve_info_after_writing;
    logic 	symbol_error, symbol_error_next;
    logic	received_at_least_one_packet_next;
    
    logic	reset_package_info;
    logic	reset_package_info_due_to_new_packet;
    logic	reset_package_info_due_to_new_transmit;
    assign	reset_package_info_due_to_new_transmit = general_inputs.start_transmit;
    
    assign	reset_package_info = reset_package_info_due_to_new_transmit || reset_package_info_due_to_new_packet;
    logic	symbol_count_error, crc_error;
    
    assign	DSI3_channel_registers_PACKET_STAT.SCE_in 			= (reset_package_info == 1'b1) ? 1'b1 : symbol_count_error;
    assign	DSI3_channel_registers_PACKET_STAT.SCE_set 			= reset_package_info | (general_inputs.response_finished  & i_enable);
    assign	DSI3_channel_registers_PACKET_STAT.CRC_ERR_in 		= ~reset_package_info;
    assign	DSI3_channel_registers_PACKET_STAT.CRC_ERR_set 		= reset_package_info | crc_error;
    assign	DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_set	= reset_package_info | (general_inputs.symbol_error_set & i_enable);
    assign	DSI3_channel_registers_PACKET_STAT.VDSI_ERR_in 		= ~reset_package_info;
    assign	DSI3_channel_registers_PACKET_STAT.VDSI_ERR_set 	= reset_package_info | (ve_flag & ~mask_ce_ve_flag_setting);
    assign	DSI3_channel_registers_PACKET_STAT.CLK_ERR_in 		= ~reset_package_info;
    assign	DSI3_channel_registers_PACKET_STAT.CLK_ERR_set 		= reset_package_info | (ce_flag & ~mask_ce_ve_flag_setting);
    
    /*###   SE - symbol error   ##################################*/
    always_comb begin // needed for the first 4 Symbols only to save the value until packet info is reset
        symbol_error_next = symbol_error;
        if (i_enable == 1'b1) begin
            if ((general_inputs.rec_pending_posedge == 1'b1) || (reset_package_info)) begin
                symbol_error_next = 1'b0;
            end
            else begin
                if (general_inputs.symbol_error_set == 1'b1)
                    symbol_error_next = 1'b1;
            end
        end
    end
    
    always_comb begin
        if (reset_package_info_due_to_new_transmit == 1'b1)
            DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_in = 1'b0;
        else begin
            if (reset_package_info_due_to_new_packet == 1'b1) begin
                DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_in = (general_inputs.symbol_error_set & i_enable);
            end
            else begin // symbol error occurs (inputs.symbol_error_set == 1'b1)
                DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR_in = 1'b1;
            end
        end
    end
    
    /*###   SYMBOL_COUNT   ##################################*/
    always_comb begin
        if (reset_package_info == 1'b1) begin
            DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_in		= '0;
        end
        else begin
            if (general_inputs.symbol_count > 9'd255) begin
                DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_in	= 8'hff;
            end
            else begin
                DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_in	= general_inputs.symbol_count[7:0];
            end
        end
    end
    assign	DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT_set	= reset_package_info | general_inputs.response_finished | general_inputs.received_data;
    
    /*###   SCE - symbol count error   ##################################*/
    always_comb begin
        symbol_count_error = 1'b0;
        if (i_enable == 1'b1) begin
            if ((general_inputs.response_finished == 1'b1)) begin
                if (general_inputs.symbol_count_overflow == 1'b1)
                    symbol_count_error = 1'b1;
                if (general_inputs.symbol_count != {1'b0, tdma_reader.packet.info.symbol_count})
                    symbol_count_error = 1'b1;
            end
        end
    end
    
    /*###   CE | VE   ##################################*/
    always_comb begin
        ce_flag_next = ce_flag | ~time_base.clkref_ok;
        ve_flag_next = ve_flag | general_inputs.ov | general_inputs.uv;
        if ((reset_ce_ve_info_after_writing == 1'b1) || (general_inputs.start_transmit == 1'b1)) begin
            ce_flag_next = ~time_base.clkref_ok;
            ve_flag_next = general_inputs.ov | general_inputs.uv;
        end
    end
    
    always_comb begin
        mask_ce_ve_flag_setting_next = mask_ce_ve_flag_setting;
        if ((general_inputs.received_data == 1'b1) || (general_inputs.start_transmit == 1'b1)) begin // received data used to not store data for less than 4 symbol "responses"
            mask_ce_ve_flag_setting_next = 1'b0;
        end
        if (reset_ce_ve_info_after_writing == 1'b1) begin
            mask_ce_ve_flag_setting_next = 1'b1;
        end
    end
    
    /*###   TE - timing error   ##################################*/
    always_comb begin
        DSI3_channel_registers_PACKET_STAT.TE_in	= ~reset_package_info;
        DSI3_channel_registers_PACKET_STAT.TE_set	= reset_package_info; 
        if(i_enable == 1'b1) begin
            if (general_inputs.rec_pending_posedge == 1'b1) begin
                DSI3_channel_registers_PACKET_STAT.TE_set = 1'b1;
                DSI3_channel_registers_PACKET_STAT.TE_in = 1'b0;
                if ((general_inputs.time_of_start_receive_after_command < tdma_reader.packet.earliest) || 
                        (general_inputs.time_of_start_receive_after_command > tdma_reader.packet.latest)
                        ) begin
                    DSI3_channel_registers_PACKET_STAT.TE_in = 1'b1;
                end
            end
            if ((i_receive_time_out_tick & general_inputs.rec_pending) == 1'b1) begin
                DSI3_channel_registers_PACKET_STAT.TE_in = 1'b1;
                DSI3_channel_registers_PACKET_STAT.TE_set = 1'b1;
            end
        end
    end
    
    /*###   CRC calculation   ######################################################*/
    sid_length_e	sid_length; 
    data_t  packet_crc, packet_crc16_next;
    data_t  seed;
    dsi3_crc_t  packet_crc8_next;
    logic	initialize_crc;
    logic	check_crc_error;
    logic   calculate_crc;
    
    dsi3_crc_parallel i_dsi3_crc_parallel (
        .i_seed      (packet_crc[7:0]   ),
        .i_data      (general_inputs.rx_data_corrected ),
        .o_crc       (packet_crc8_next  ));
    
    always_comb begin
        if (initialize_crc == 1'b1) begin
            packet_crc16_next = seed;
        end
        else begin
            if (sid_length == SID_16Bit_CRC)
                packet_crc16_next = crc_ccitt_16_word(packet_crc, general_inputs.rx_data_corrected);
            else begin
                packet_crc16_next[15:8] = '0;
                packet_crc16_next[ 7:0] = packet_crc8_next;
            end
        end
    end
    
    assign	sid_length = sid_length_e'(tdma_reader.packet.info.id_config);
    
    always_comb begin
        case (sid_length)
            SID_0Bit: seed = SEED_8Bit_CRC;
            SID_4Bit: seed = {12'h000, general_inputs.rx_data_corrected[15:12]};
            SID_8Bit: seed = {8'h00, general_inputs.rx_data_corrected[15:8]};
            SID_16Bit_CRC: seed = SEED_16Bit_CRC;
        endcase
    end
    
    always_comb begin
        crc_error = 1'b0;
        if (check_crc_error == 1'b1) begin
            if (common_config.crc_enable == 1'b1) begin
                if (packet_crc != '0) begin
                    crc_error = 1'b1;
                end
                if (general_inputs.symbol_count > 9'd255) begin
                    crc_error = 1'b1;
                end
            end
        end
    end
    
    /*###   TDMA infos   ######################################################*/
    timebase_t  time_in_period, packet_border;
    logic   packet_too_late;
    assign  time_in_period  = time_base.base_time - general_inputs.time_of_start_transmit;
    
    always_comb begin
        if (8'(tdma_reader.header.packet_count.packet_count - 4'd1) == packet_index) begin
            packet_border = tdma_reader.header.period;
        end
        else begin
            packet_border = ((tdma_reader.packet_next.earliest - tdma_reader.packet.latest) >> 1) + tdma_reader.packet.latest; //P52144-186
        end
    end
    
    assign  tdma_header_packet_count = packet_counter_t'(tdma_reader.header.packet_count.packet_count);
    
    packet_counter_t    tdma_packet_index;
    assign  tdma_packet_index = {4'h0,tdma_reader.packet_index};
    
    always_comb begin
        packet_too_late = 1'b0;
        if (packet_index == tdma_packet_index) begin
            if ((time_in_period > packet_border) && (general_inputs.rec_pending == 1'b0))
                packet_too_late = time_base.tick_1us;
        end
    end
    
    logic[6:0] word_counter, word_counter_next;
    logic[6:0] word_count_of_current_packet;
    
    always_comb begin
        word_count_of_current_packet = {1'b0, tdma_reader.packet.info.symbol_count[7:2]};
        if (tdma_reader.packet.info.symbol_count[1:0] != '0)
            word_count_of_current_packet += 7'd1;
    end
    
    /*###   data FSM   ######################################################*/
    typedef enum logic[3:0] {
        DATA_IDLE, 
        DATA_WRITE_EMPTY_FRAME_HEADER, 
        DATA_WRITE_EMPTY_PACKET_HEADER, 
        DATA_STORE_DATA, 
        DATA_VALIDATE, 
        DATA_INVALIDATE, 
        DATA_FINISH_PACKET, 
        DATA_FINISH_FRAME, 
        DATA_CLEAR_BUFFER, 
        DATA_WAIT_FOR_PACKET,
        DATA_WAIT_FOR_DATA,
        DATA_WRITE_EMPTY_DATA,
        DATA_INITIALIZE_TDMA, 
        DATA_READ_NEXT_TDMA_PACKET
    } data_state_e;
    
    data_state_e	data_state, data_state_next, data_state_last, data_state_last_next;
    logic	handle_clear_buffer, handle_clear_buffer_next;
    logic	handle_invalidate_buffer, handle_invalidate_buffer_next;
    logic	invalidate_buffer, invalidate_buffer_next;
    
    logic	handle_received_data, handle_received_data_next;
    logic	handle_response_finished, handle_response_finished_next;
    
    logic   handle_start_transmit, handle_start_transmit_next;
    logic   handle_receive_timeout, handle_receive_timeout_next;
    logic   handle_stop, handle_stop_next;
    
    logic   update_pc_flag;
    
    assign  DSI3_channel_registers_FRAME_STAT.PC_set = reset_frame_info || update_pc_flag;
    assign  DSI3_channel_registers_FRAME_STAT.PACKET_COUNT_in = packet_counter;
    always_comb begin
        if (reset_frame_info == 1'b1) begin
            DSI3_channel_registers_FRAME_STAT.PC_in = 1'b0;
        end
        else begin
            if (packet_counter > {4'h0, tdma_reader.header.packet_count.packet_count}) begin
                DSI3_channel_registers_FRAME_STAT.PC_in = 1'b1;
            end
            else begin
                DSI3_channel_registers_FRAME_STAT.PC_in = 1'b0;
            end
        end
    end
    
    always_ff @(posedge clk_rst.clk or negedge clk_rst.rstn) begin
        if (clk_rst.rstn == 1'b0)  begin
            data_state		<= DATA_IDLE;
            data_state_last	<= DATA_IDLE;
            packet_crc		<= 16'hffff;
            handle_invalidate_buffer <= 1'b0;
            handle_clear_buffer      <= 1'b0;
            handle_start_transmit    <= 1'b0;
            handle_response_finished <= 1'b0;
            handle_received_data     <= 1'b0;
            handle_receive_timeout   <= 1'b0;
            handle_stop              <= 1'b0;
            invalidate_buffer <= 1'b0;
            ve_flag			<= 1'b0;
            ce_flag			<= 1'b0;
            mask_ce_ve_flag_setting <= 1'b1;
            o_received_at_least_one_packet <= 1'b0;
            symbol_error	<= 1'b0;
            packet_counter  <= '0;
            packet_index    <= '0;
            word_counter    <= '0;
        end
        else begin
            data_state		<= data_state_next;
            data_state_last	<= data_state_last_next;
            handle_invalidate_buffer <= handle_invalidate_buffer_next;
            handle_clear_buffer	     <= handle_clear_buffer_next;
            handle_received_data     <= handle_received_data_next;
            handle_response_finished <= handle_response_finished_next;
            handle_start_transmit    <= handle_start_transmit_next;
            handle_receive_timeout   <= handle_receive_timeout_next;
            handle_stop              <= handle_stop_next;
            invalidate_buffer <= invalidate_buffer_next;
            ce_flag			<= ce_flag_next;
            ve_flag			<= ve_flag_next;
            mask_ce_ve_flag_setting <= mask_ce_ve_flag_setting_next;
            o_received_at_least_one_packet <= received_at_least_one_packet_next;
            symbol_error	<= symbol_error_next;
            packet_counter  <= packet_counter_next;
            packet_index    <= packet_index_next;
            word_counter    <= word_counter_next;
            if ((calculate_crc == 1'b1) | (initialize_crc == 1'b1))
                packet_crc <= packet_crc16_next;
        end
    end
    
    always_comb begin
        recalculate_ecc = 1'b0;
        data_state_next = data_state;
        dsi_data_writer = general_inputs.rx_data_corrected;
        pdcm_data_writer.action = PDCM_IDLE_WRITE;
        calculate_crc = 1'b0;
        check_crc_error = 1'b0;
        invalidate_buffer_next = invalidate_buffer | general_inputs.transceiver_enable_negedge;
        
        handle_clear_buffer_next = handle_clear_buffer | i_clear_data_buffer;
        handle_invalidate_buffer_next = handle_invalidate_buffer | i_clear_and_invalidate_data_buffer;
        handle_received_data_next = handle_received_data | (general_inputs.received_data & i_enable);
        handle_response_finished_next = handle_response_finished | (general_inputs.response_finished & i_enable) | (general_inputs.rec_pending_negedge & i_enable);
        handle_start_transmit_next = (general_inputs.start_transmit & i_enable) | handle_start_transmit;
        handle_receive_timeout_next = handle_receive_timeout | (i_receive_time_out_tick & i_enable);
        handle_stop_next = handle_stop | i_stop;
        
        initialize_crc = 1'b0;
        
        reset_ce_ve_info_after_writing = 1'b0;
        data_state_last_next = data_state_last;
        
        o_hw_fail_data_fsm = 1'b0;
        
        received_at_least_one_packet_next = o_received_at_least_one_packet & ~i_clear_flag_for_received_packets;
        
        tdma_reader.action = NO_READ_ACTION;
        reset_frame_info = 1'b0;
        reset_package_info_due_to_new_packet = 1'b0;
        packet_counter_next = packet_counter;
        packet_index_next   = packet_index;
        
        update_pc_flag = 1'b0;
        
        word_counter_next = word_counter;
        
        case (data_state)
            DATA_IDLE: begin
                handle_response_finished_next = 1'b0;
                handle_stop_next = 1'b0;
                if ((i_clear_data_buffer == 1'b1) || (handle_clear_buffer)) begin
                    data_state_next = DATA_CLEAR_BUFFER;
                    data_state_last_next = DATA_IDLE;
                end
                else begin
                    if (i_enable == 1'b1) begin
                        if (handle_start_transmit == 1'b1) begin
                            data_state_next = DATA_INITIALIZE_TDMA;
                            handle_received_data_next = 1'b0;
                            handle_response_finished_next = 1'b0;
                            handle_start_transmit_next = 1'b0;
                            handle_receive_timeout_next = 1'b0;
                            packet_counter_next = '0;
                            packet_index_next   = '0;
                            reset_frame_info = 1'b1;
                        end
                    end
                end
            end
            DATA_INITIALIZE_TDMA: begin
                tdma_reader.action = INITIALIZE;
                if(tdma_reader.acknowledge == 1'b1) begin
                    data_state_next = DATA_WRITE_EMPTY_FRAME_HEADER;
                end
            end
            DATA_READ_NEXT_TDMA_PACKET: begin
                if (packet_index < tdma_header_packet_count) begin
                    tdma_reader.action = READ_NEXT_PACKET;
                    if(tdma_reader.acknowledge == 1'b1) begin
                        reset_package_info_due_to_new_packet = 1'b1;
                        data_state_next = DATA_WAIT_FOR_PACKET;
                    end
                end
                else begin // do not read next TDMA packet if there is none!
                    data_state_next = DATA_WAIT_FOR_PACKET;
                end
            end
            DATA_WRITE_EMPTY_FRAME_HEADER: begin
                recalculate_ecc = 1'b1;
                pdcm_data_writer.action = PDCM_BUFFER_WRITE_FRAME_HEADER;
                dsi_data_writer = DSI3_channel_registers_FRAME_STAT.value;
                if (pdcm_data_writer.ready == 1'b1) begin
                    data_state_next = DATA_WAIT_FOR_PACKET;
                end
                packet_counter_next = '0;
                packet_index_next   = '0;
            end
            DATA_WAIT_FOR_PACKET: begin
                if ((i_clear_data_buffer == 1'b1) || (handle_clear_buffer)) begin
                    data_state_next = DATA_CLEAR_BUFFER;
                    data_state_last_next = DATA_WAIT_FOR_PACKET;
                end
                else begin
                    //#####   end of frame   #####
                    if ((handle_receive_timeout == 1'b1) || (handle_stop == 1'b1)) begin
                        if (packet_index < tdma_header_packet_count) begin
                            data_state_next = DATA_WRITE_EMPTY_PACKET_HEADER;
                            word_counter_next = '0;
                            data_state_last_next = DATA_WRITE_EMPTY_DATA;
                            packet_index_next = packet_index + packet_counter_t'(1);
                            if (general_inputs.rec_pending_negedge) begin
                                if (packet_counter != '1)
                                    packet_counter_next = packet_counter + packet_counter_t'(1);
                            end
                        end
                        else begin // no more packets to store in frame
                            data_state_next = DATA_FINISH_FRAME;
                            handle_receive_timeout_next = 1'b0;
                            update_pc_flag = 1'b1;
                        end
                    end
                    else begin
                        if (packet_counter < tdma_header_packet_count) begin
                            //#####   receive new packet   #####
                            if (((general_inputs.received_data == 1'b1) || (handle_received_data == 1'b1)) && (packet_counter < tdma_header_packet_count)) begin
                                initialize_crc = 1'b1;
                                data_state_next = DATA_WRITE_EMPTY_PACKET_HEADER;
                                data_state_last_next = DATA_WAIT_FOR_DATA;
                                word_counter_next = '0;
                                handle_response_finished_next = general_inputs.response_finished;
                                packet_index_next   = packet_index   + packet_counter_t'(1);
                                if (packet_counter != '1)
                                    packet_counter_next = packet_counter + packet_counter_t'(1);
                            end
                            else begin
                                //#####   no packet in time   #####
                                if (general_inputs.rec_pending == 1'b0) begin
                                    if (packet_too_late == 1'b1) begin
                                        data_state_next = DATA_WRITE_EMPTY_PACKET_HEADER;
                                        data_state_last_next = DATA_WRITE_EMPTY_DATA;
                                        word_counter_next = '0;
                                        packet_index_next = packet_index   + packet_counter_t'(1);
                                    end
                                end
                            end
                        end
                        else begin
                            //#####   more packets in frame as expected   #####
                            handle_received_data_next = 1'b0;
                            if (handle_response_finished == 1'b1) begin
                                if (packet_counter != '1)
                                    packet_counter_next = packet_counter + packet_counter_t'(1);
                                handle_response_finished_next = 1'b0;
                            end
                        end
                    end
                end
            end
            DATA_WRITE_EMPTY_PACKET_HEADER: begin
                recalculate_ecc = 1'b1;
                pdcm_data_writer.action = PDCM_BUFFER_WRITE_PACKET_HEADER;
                dsi_data_writer = DSI3_channel_registers_PACKET_STAT.value;
                word_counter_next = '0;
                if (pdcm_data_writer.ready == 1'b1) begin
                    data_state_next = data_state_last;
                end
            end
            DATA_WRITE_EMPTY_DATA : begin
                pdcm_data_writer.action = PDCM_BUFFER_WRITE;
                recalculate_ecc = 1'b1;
                dsi_data_writer = '0;
                if (pdcm_data_writer.ready == 1'b1) begin
                    data_state_next = DATA_FINISH_PACKET;
                    word_counter_next = word_counter + 7'd1;
                end
            end
            DATA_WAIT_FOR_DATA : begin
                if ((i_clear_data_buffer == 1'b1) || (handle_clear_buffer)) begin
                    data_state_next = DATA_CLEAR_BUFFER;
                    data_state_last_next = DATA_WAIT_FOR_DATA;
                end
                else begin
                    if (handle_response_finished == 1'b1) begin
                        data_state_next = DATA_FINISH_PACKET;
                        check_crc_error = 1'b1;
                    end
                    else begin
                        if ((general_inputs.received_data == 1'b1) || (handle_received_data == 1'b1)) begin
                            if (handle_received_data == 1'b1) begin
                                handle_received_data_next = general_inputs.received_data;
                            end
                            else begin
                                handle_received_data_next = 1'b0;
                            end
                            if ((general_inputs.symbol_count <= {1'b0, tdma_reader.packet.info.symbol_count}) || 
                                (general_inputs.symbol_count == 9'h100 && tdma_reader.packet.info.symbol_count > 8'hfc  )) begin
                                data_state_next = DATA_STORE_DATA;
                                calculate_crc = 1'b1;
                            end
                        end
                        else begin
                            if (general_inputs.response_finished == 1'b1) begin // handle_response_finished is 1'b0 first if-clause
                                data_state_next = DATA_FINISH_PACKET;
                                check_crc_error = 1'b1;
                            end
                        end
                    end
                end
            end
            DATA_STORE_DATA: begin
                if (((i_enable == 1'b1) && (general_inputs.symbol_count <= 9'h100))) begin
                    pdcm_data_writer.action = PDCM_BUFFER_WRITE;
                    if (pdcm_data_writer.ready == 1'b1) begin
                        data_state_next = DATA_WAIT_FOR_DATA;
                        word_counter_next = word_counter + 7'd1;
                    end
                end
                else begin
                    data_state_next = DATA_WAIT_FOR_DATA;
                end
            end
            DATA_FINISH_PACKET: begin 
                if (word_counter < word_count_of_current_packet) begin
                    data_state_next = DATA_WRITE_EMPTY_DATA;
                end
                else begin
                    recalculate_ecc = 1'b1;
                    pdcm_data_writer.action = PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN;
                    dsi_data_writer = DSI3_channel_registers_PACKET_STAT.value;
                    if (pdcm_data_writer.ready == 1'b1) begin
                        received_at_least_one_packet_next = 1'b1;
                        data_state_next = DATA_READ_NEXT_TDMA_PACKET;
                        handle_response_finished_next = 1'b0;
                        reset_ce_ve_info_after_writing = 1'b1;
                    end
                end
            end
            DATA_FINISH_FRAME: begin
                recalculate_ecc = 1'b1;
                pdcm_data_writer.action = PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN;
                dsi_data_writer = DSI3_channel_registers_FRAME_STAT.value;
                if (pdcm_data_writer.ready == 1'b1) begin
                    data_state_next = DATA_VALIDATE;
                end
            end
            DATA_VALIDATE: begin
                pdcm_data_writer.action = PDCM_BUFFER_VALIDATE;
                if (pdcm_data_writer.ready == 1'b1) begin
                    data_state_next = DATA_IDLE;
                end
                handle_response_finished_next = 1'b0;
            end
            DATA_INVALIDATE: begin
                pdcm_data_writer.action = PDCM_BUFFER_INVALIDATE;
                if (pdcm_data_writer.ready == 1'b1) begin
                    data_state_next = DATA_IDLE;
                end
                handle_response_finished_next = 1'b0;
                invalidate_buffer_next = 1'b0;
            end
            DATA_CLEAR_BUFFER: begin
                if(handle_invalidate_buffer == 1'b1)
                    pdcm_data_writer.action = PDCM_BUFFER_CLEAR_AND_INVALIDATE_NEXT;
                else 
                    pdcm_data_writer.action = PDCM_BUFFER_CLEAR;
                if (pdcm_data_writer.ready == 1'b1) begin
                    handle_clear_buffer_next = 1'b0;
                    handle_invalidate_buffer_next = 1'b0;
                    data_state_next = data_state_last;
                end
            end
            default: begin
                data_state_last_next = DATA_INVALIDATE;
                data_state_next = DATA_CLEAR_BUFFER;	
                o_hw_fail_data_fsm = 1'b1;
            end
        endcase
        if ((invalidate_buffer | general_inputs.transceiver_enable_negedge) == 1'b1) begin
            data_state_next = DATA_INVALIDATE;
        end
    end
    
endmodule