/**
 * Module: dsi3_block
 *
 * module for one DSI3 channel
 */
module dsi3_block import project_pkg::*; #(
		parameter shortint BASE_ADDR,
		parameter shortint BASE_ADDR_TDMA,
		parameter shortint BASE_ADDR_TEST,
		parameter shortint BASE_ADDR_TRIMMING,
		parameter int ADDR_WIDTH,
		parameter int CHANNEL
	) (
		clk_reset_if.slave               clk_rst,
		buffer_reader_if.master          command_reader,
        pdcm_buffer_writer_if.master     pdcm_data_writer,
		buffer_writer_if.master          crm_data_writer,
		
		dsi3_io_if.dsi3_block            dsi3_io,
		dsi3_common_config_if.dsi3_block common_config,
		timebase_info_if.slave           time_base,
		
		synchronization_if.master        sync,
		
		dsi3_start_request_if.master     request,
		
		tmr_dsi_if.master                tmr_dsi,
		tmr_out_dsi_if.master            tmr_out_dsi,
		jtag_bus_if.slave                jtag_bus,
		output	jtag_dr_for_registers_t  o_jtag_dr,
		
		elip_if.slave                    elip_registers,
		output	elip_data_t              o_elip_register_read,
		elip_full_if.master              elip_tdma,
		
		input	logic                    i_transceiver_enable,
		
		input	logic                    i_clear_pdcm_data_buffer,
		input	logic                    i_clear_crm_data_buffer,
		input	logic                    i_clear_and_invalidate_crm_data_buffer,
		input	logic                    i_clear_and_invalidate_pdcm_data_buffer,
		input	logic                    i_stop_transmission,
		input	logic                    i_sync_error,
        input   logic                    i_set_command_error,
        input   logic                    i_invalidate_tdma_scheme,
		
		output	logic                    o_interrupt,
		
		output	logic                    o_transmit_pending,
		output	logic                    o_hard_ware_error_irq,
		output	logic                    o_hard_ware_error,
		output	logic                    o_tmr_dig_prevent_deactivation,
		
		ecc_error_if.master              ecc_error_cmd,
		ecc_error_if.master              ecc_error_data,
        ecc_error_if.master              ecc_error_tdma,
		
		output	logic                    o_busy,
		output	logic                    o_hw_fail,
		output	logic                    o_clear_command_queue,
		output	logic					 o_no_tdma_scheme_defined,
        output  data_t                   o_tdma_frame_word_count
	);
	
	import spi_implementation_pkg::*;
	import dsi3_pkg::*;
	import buffer_if_pkg::*;
	import tdma_pkg::*;
	
	/*###   signal definitions   ######################################################*/
	dsi_command_control_state_e state, state_next;
	spi_command_t command;
	data_ecc_t  data_high, data_low, data_low_crc;
	logic	broad_cast, broad_cast_next;
	logic	acknowledge, finished;
	channel_mode_t mode;
	typedef struct {
		logic       unlimited;
		logic [7:0] periods;
	} period_t;
	period_t periods, periods_next;
	dsi3_crc_t	seed, crc, crc_next;
	logic	uv_sync, ov_sync;
	logic	uv_deb, ov_deb;
	
	logic	stop_and_clear_buffer, stop_and_clear_buffer_next;
	logic	hw_fail_core, hw_fail_tdma_manager, hw_fail_iload;
	
	logic	pdcm_in_progress_next;
	logic	set_period;
	logic	tdma_scheme_valid;
    
    logic   set_pdcm_err, set_com_err, set_iq_err;
    
	tdma_packet_ecc_t	tdma_packet;
	tdma_header_ecc_t	tdma_header;
	
	tdma_writer_if 	tdma_writer ();
    tdma_reader_if  tdma_reader ();
    
	logic 	store_data_high, store_data_low;
    logic   store_earliest, store_latest, store_packet_info;
    logic   store_period, store_packet_count;
    logic   store_command, reset_command;
    
    logic   start_quiescent_current, ready_quiescent_current;
    
    logic   clear_pdcm_data_buffer, clear_pdcm_data_buffer_due_to_tdma_change, clear_pdcm_data_buffer_due_to_tdma_error;
    assign  clear_pdcm_data_buffer = i_clear_pdcm_data_buffer | clear_pdcm_data_buffer_due_to_tdma_change | clear_pdcm_data_buffer_due_to_tdma_error;
    
    logic   stop_transmit_or_receive;
    	
	/*###   ecc decoder - data_low correction  #####################################*/
	
	logic[DATA_WIDTH-1:0] command_reader_data_corrected;
	logic data_ecc_single;
	logic data_ecc_double;
	ecc_error_if ecc_error_cmd_int ();
	
	edge_detect i_edge_detect_single_error (
		.clk_rst (clk_rst                                         ),
		.i_signal(data_ecc_single | ecc_error_cmd_int.single_error),
		.o_edge  (ecc_error_cmd.single_error                      ));
	
	edge_detect i_edge_detect_double_error (
		.clk_rst (clk_rst                                         ),
		.i_signal(data_ecc_double | ecc_error_cmd_int.double_error),
		.o_edge(ecc_error_cmd.double_error                      ));
	
	ecc_decoder #(
		.DATA_WIDTH(DATA_WIDTH),
		.ECC_WIDTH (ECC_WIDTH )
	) i_ecc_dec_command_reader_data (
		.i_correct_n(1'b0                         ),
		.i_data     (command_reader.data.data     ),
		.i_ecc      (command_reader.data.ecc      ),
		.o_data     (command_reader_data_corrected),
		.o_ecc_cor  (data_ecc_single              ),
		.o_ecc_err  (data_ecc_double              ));
	
	/*###   ecc encoder   ##########################################################*/
	ecc_t data_low_crc_ecc;
	ecc_encoder #(
		.DATA_WIDTH(DATA_WIDTH),
		.ECC_WIDTH (ECC_WIDTH )
	) i_ecc_enc_crc (
		.i_data(data_low_crc.data),
		.o_ecc (data_low_crc_ecc ));
	
	/*###   synchronization & debouncing   ######################################################*/
	sync_deb_long #(
		.DEBOUNCE_TIME(5   ),
		.RESET_VALUE  (1'b0)
	) i_sync_deb_uv (
		.clk_rst        (clk_rst                          ),
		.i_in           (dsi3_io.uv & i_transceiver_enable),
		.i_debounce_tick(time_base.tick_1ms               ),
		.o_out          (uv_deb                           ),
		.o_test_out     (tmr_out_dsi.uv_synced            ),
		.o_out_synced   (uv_sync                          ));
	
	sync_deb_long #(
		.DEBOUNCE_TIME(5   ),
		.RESET_VALUE  (1'b0)
	) i_sync_deb_ov (
		.clk_rst        (clk_rst              ),
		.i_in           (dsi3_io.ov           ),
		.i_debounce_tick(time_base.tick_1ms   ),
		.o_out          (ov_deb               ),
		.o_test_out     (tmr_out_dsi.ov_synced),
		.o_out_synced   (ov_sync              ));
	
	assign	o_hard_ware_error_irq = DSI3_channel_registers_DSI_IRQ_STAT.DSIOV | DSI3_channel_registers_DSI_IRQ_STAT.DSIUV;
	assign	o_hard_ware_error = ov_deb | uv_deb;
	
	logic	transceiver_started_up;
	enable_counter #(
		.DEBOUNCE_TIME(10  ),
		.RESET_VALUE  (1'b0)
	) enable_counter (
		.clk_rst        (clk_rst               ),
		.i_in           (i_transceiver_enable  ),
		.i_debounce_tick(time_base.tick_1us    ),
		.o_out          (transceiver_started_up));
	
	/*###   synchronization   ######################################################*/
	logic tick_1us, start_tick_1us;
	tick_gen #(
		18
	) i_tick_1us (
		.clk_rst   (clk_rst        ),
		.reset_sync(~start_tick_1us),
		.tick_out  (tick_1us       ));
	
	/*###   block registers   ######################################################*/
	`include "DSI3_channel_registers_if_inst.sv"
	`include "DSI3_channel_trimming_registers_if_inst.sv"
	
	elip_data_t              elip_register_read_trimming, elip_register_read_channel_regs;
	
	DSI3_channel_trimming_registers #(
		.base_addr(BASE_ADDR_TRIMMING),
		.addr_width(ADDR_WIDTH)
	) i_DSI3_channel_trimming_registers (
		.clk_rst                                          (clk_rst                                                 ),
		.addr                                             (elip_registers.addr                                     ),
		.data_in                                          (elip_registers.data_write                               ),
		.wr                                               (elip_registers.wr                                       ),
		.rd                                               (elip_registers.rd                                       ),
		.data_out                                         (elip_register_read_trimming                             ),
		.DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL(DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.master),
		.DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE(DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.master)
	);
	
	DSI3_channel_registers #(
		.base_addr (BASE_ADDR ),
		.addr_width(ADDR_WIDTH)
	) i_DSI3_channel_registers (
		.clk_rst                                 (clk_rst                                        ),
		.addr                                    (elip_registers.addr                            ),
		.data_in                                 (elip_registers.data_write                      ),
		.wr                                      (elip_registers.wr                              ),
		.rd                                      (elip_registers.rd                              ),
		.data_out                                (elip_register_read_channel_regs                ),
		.DSI3_channel_registers_SYNC             (DSI3_channel_registers_SYNC.master             ),
		.DSI3_channel_registers_DSI_STAT         (DSI3_channel_registers_DSI_STAT.master         ),
		.DSI3_channel_registers_DSI_IRQ_STAT     (DSI3_channel_registers_DSI_IRQ_STAT.master     ),
		.DSI3_channel_registers_DSI_IRQ_MASK     (DSI3_channel_registers_DSI_IRQ_MASK.master     ),
		.DSI3_channel_registers_DSI_CMD          (DSI3_channel_registers_DSI_CMD.master          ),
		.DSI3_channel_registers_CRM_WORD2        (DSI3_channel_registers_CRM_WORD2.master        ),
		.DSI3_channel_registers_CRM_WORD1        (DSI3_channel_registers_CRM_WORD1.master        ),
		.DSI3_channel_registers_PACKET_STAT      (DSI3_channel_registers_PACKET_STAT.master      ),
		.DSI3_channel_registers_WAIT_TIME        (DSI3_channel_registers_WAIT_TIME.master        ),
		.DSI3_channel_registers_PDCM_PERIOD      (DSI3_channel_registers_PDCM_PERIOD.master      ),
		.DSI3_channel_registers_FRAME_STAT       (DSI3_channel_registers_FRAME_STAT.master       ),
		.DSI3_channel_registers_DSI_LOAD         (DSI3_channel_registers_DSI_LOAD.master         ));
	
	assign	o_elip_register_read = elip_register_read_channel_regs | elip_register_read_trimming;
	
	assign	o_interrupt = |(DSI3_channel_registers_DSI_IRQ_STAT.value &  DSI3_channel_registers_DSI_IRQ_MASK.value);
	
	assign	DSI3_channel_registers_DSI_STAT.DSIUV_in = uv_sync;
	assign	DSI3_channel_registers_DSI_STAT.DSIOV_in = ov_sync;
	
	assign	DSI3_channel_registers_DSI_IRQ_STAT.DSIOV_set = ov_deb;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.DSIOV_in = 1'b1;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.DSIUV_in = 1'b1;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.DSIUV_set = uv_deb;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.DMOF_in = 1'b1;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR_in = 1'b1;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR_set = i_sync_error;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR_in = 1'b1; 
	assign	DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR_set = set_pdcm_err | set_com_err | i_set_command_error;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR_in = 1'b1;
	assign	DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR_set = set_iq_err;
    
	
	assign	DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL_in = 1'b1;
	
	assign	DSI3_channel_registers_SYNC.PIN_in = sync.currently_registered_channels[DSI_CHANNELS];
	assign	DSI3_channel_registers_SYNC.CHANNELS_in = sync.currently_registered_channels[DSI_CHANNELS-1:0];
	
	assign	o_hw_fail = DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL;
	
	// limitation of PDCM Period
	always_comb begin
		DSI3_channel_registers_PDCM_PERIOD.PDCMPER_set = set_period;
		if (set_period == 1'b1) begin
			if (command_reader_data_corrected < elip_data_t'(100)) begin
				DSI3_channel_registers_PDCM_PERIOD.PDCMPER_in = 16'd100;
			end
			else begin
				if (command_reader_data_corrected > elip_data_t'(65520)) begin
					DSI3_channel_registers_PDCM_PERIOD.PDCMPER_in = 16'd65520;
				end
				else begin
					DSI3_channel_registers_PDCM_PERIOD.PDCMPER_in = command_reader_data_corrected;
				end
			end
		end
		else begin
			DSI3_channel_registers_PDCM_PERIOD.PDCMPER_in = DSI3_channel_registers_PDCM_PERIOD.PDCMPER;
		end
    end
    
	/*###   FFs   ######################################################*/
	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin
		if (clk_rst.rstn == 1'b0) begin
			state <= dsi3_pkg::IDLE;
			command <= '0;
			broad_cast <= 1'b0;
            data_high <= EMPTY_DATA;
			data_low <= EMPTY_DATA;
			periods <= '{1'b0, 'd0};
			crc		<= 8'hff;
			stop_and_clear_buffer <= 1'b0;
			tdma_packet <= EMPTY_TDMA_PACKET;
			tdma_header <= EMPTY_TDMA_HEADER;
		end
		else begin
			state <= state_next;
			broad_cast <= broad_cast_next;
			stop_and_clear_buffer <= stop_and_clear_buffer_next;
			periods	<= periods_next;
            if (reset_command == 1'b1)      command <= '0;
            else begin
                if (store_command == 1'b1)  command      <= command_reader_data_corrected;
            end
			if (store_data_high == 1'b1)    data_high    <= command_reader.data;
			if (store_data_low == 1'b1)     data_low     <= command_reader.data;
            if (store_earliest == 1'b1)     tdma_packet.earliest <= command_reader.data;
            if (store_latest == 1'b1)       tdma_packet.latest   <= command_reader.data; 
            if (store_packet_info == 1'b1)  tdma_packet.info     <= command_reader.data;
            if (store_period == 1'b1)       tdma_header.period   <= command_reader.data;
            if (store_packet_count == 1'b1) tdma_header.packet_count <= command_reader.data;
			if ((store_data_high == 1'b1) || (store_data_low == 1'b1))	crc <= crc_next;
		end
    end
	
	assign	command_reader.step = '0;
	logic	request_acknowledge;
	assign	request.mode = mode;
	assign	request.pdcm_period = DSI3_channel_registers_PDCM_PERIOD.PDCMPER;
	assign	request.transmitting = o_transmit_pending;
	
	assign	request.pdcm_in_progress = pdcm_in_progress_next;
	
	/*###   FSM   ######################################################*/
	
	`define start_pdcm	request_acknowledge = 1'b1; \
		if (acknowledge == 1'b1) begin \
			state_next = DSI_PDCM_WAIT; \
		end \
    
    `define stop_transmission_clause( _when_stopping_ ) state_next = dsi3_pkg::IDLE; \
            stop_and_clear_buffer_next = 1'b0; \
            sync.reset = 1'b1; \
            stop_transmit_or_receive = 1'b1; \
            _when_stopping_
    
	`define if_stop_transmission( _when_stopping_ )  if (i_stop_transmission == 1'b1) begin \
            `stop_transmission_clause( _when_stopping_ ) \
		end
	
    `define if_stop_transmission_iload( _when_stopping_ )  if ((i_stop_transmission == 1'b1) || (hw_fail_iload)) begin \
            state_next = dsi3_pkg::IDLE; \
            stop_and_clear_buffer_next = 1'b0; \
            sync.reset = 1'b1; \
            _when_stopping_ \
        end
    
	`define do_error_handling(_is_hardware_fail_)	state_next = dsi3_pkg::IDLE; \
		sync.reset = 1'b1; \
		periods_next.periods = '0; \
		periods_next.unlimited = 1'b0; \
		stop_and_clear_buffer_next = 1'b1; \
		o_clear_command_queue = 1'b1; \
        stop_transmit_or_receive = 1'b1; \
		DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL_set = _is_hardware_fail_ | hw_fail_core | hw_fail_tdma_manager | hw_fail_iload; \
	
    always_comb begin
        reset_command = 1'b0;
        if (state_next == dsi3_pkg::IDLE) begin
            if (state != dsi3_pkg::IDLE) begin
                reset_command = 1'b1;
            end
        end
    end
    
	always_comb begin
		command_reader.action = IDLE_READ;
		store_data_high = 1'b0;
		store_data_low = 1'b0;
		broad_cast_next = broad_cast;
		mode = MODE_CRM;
		periods_next = periods;
		DSI3_channel_registers_WAIT_TIME.TIME_set = 1'b0;
		DSI3_channel_registers_WAIT_TIME.TIME_in = DSI3_channel_registers_WAIT_TIME.TIME;
		
		sync.register = 1'b0;
		sync.waiting = 1'b0;
		sync.channels_to_sync = '0;
		sync.reset = 1'b0;
		
		stop_and_clear_buffer_next = i_stop_transmission | stop_and_clear_buffer;
		
		state_next = state;
		
		start_tick_1us = 1'b0;
		
		request.request = 1'b0;
		pdcm_in_progress_next = 1'b0;
		
		request_acknowledge = 1'b0;
		DSI3_channel_registers_DSI_STAT.SYNC_in = 1'b0;
		
		DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL_set = hw_fail_core | hw_fail_tdma_manager | hw_fail_iload;
		
		o_busy = 1'b1;
		o_clear_command_queue = 1'b0;
		
		set_period = 1'b0;
        set_com_err = 1'b0; 
        set_iq_err = 1'b0;
        set_pdcm_err = 1'b0;
		
		tdma_writer.action = NO_ACTION;
        
        store_earliest      = 1'b0;
        store_latest        = 1'b0;
        store_packet_info   = 1'b0;
        store_period        = 1'b0;
        store_packet_count  = 1'b0;
        store_command       = 1'b0;
        
        start_quiescent_current = 1'b0;
        clear_pdcm_data_buffer_due_to_tdma_change = 1'b0;
        
        stop_transmit_or_receive = 1'b0;
		
		case (state)
			dsi3_pkg::IDLE: begin
				o_busy = 1'b0;
				stop_and_clear_buffer_next = 1'b0;
				if ((command_reader.empty == 1'b0) && (i_stop_transmission == 1'b0) && (stop_and_clear_buffer == 1'b0) && (transceiver_started_up == 1'b1)) begin
					command_reader.action = BUFFER_READ;
					if (command_reader.ready == 1'b1) begin
						state_next = DECODE;
                        store_packet_count = 1'b1;
                        store_command = 1'b1;
					end
				end
				periods_next.periods = '0;
				periods_next.unlimited = '0;
				if ((i_stop_transmission == 1'b1) || (stop_and_clear_buffer == 1'b1)) begin
					sync.reset = 1'b1;
					stop_and_clear_buffer_next = 1'b0;
				end
			end
			DECODE: begin
				`if_stop_transmission()
				else begin
					if (command.data[LSB_CHANNEL_SELECT+CHANNEL] != 1'b1) begin // check for correct channel selection
						`do_error_handling(1'b1)
					end
					else begin
						case (command.command)
							DSI_CRM: begin
								state_next = DSI_CRM_GET_DATA_HIGH;
								broad_cast_next = command[BIT_NO_RESPONSE];
							end
							DSI_PDCM: begin
								if (command.data[MSB_PDCM_PERIODS:LSB_PDCM_PERIODS]==8'd0)
									periods_next = '{unlimited: 1'b1, periods: 8'd0};
								else
									periods_next = '{unlimited: 1'b0, periods: command.data[MSB_PDCM_PERIODS:LSB_PDCM_PERIODS]};
								state_next = DSI_PDCM_WAIT_FOR_START;
								broad_cast_next = 1'b0;
							end
							DSI_UPLOAD_TDMA: begin
								if (command.data[TDMA_PACKET_OR_VALIDATE_SELECT] == UPLOAD_PACKET) begin
									state_next = DSI_UPLOAD_TDMA_PACKET_EARLIEST;
                                    clear_pdcm_data_buffer_due_to_tdma_change = 1'b1;
								end
								else begin
									state_next = DSI_VALIDATE_TDMA_PERIOD;
                                    clear_pdcm_data_buffer_due_to_tdma_change = 1'b1;
								end
							end
							DSI_WAIT: begin
								state_next = DSI_READ_WAIT_TIME;
                            end
                            DSI_ILOAD: begin
                                state_next = DSI_ILOAD_WAIT_FOR_START;
                            end
							SYNC: begin
								state_next = DSI_SYNC_START;
							end
							DSI_START_DISCOVERY: begin
								state_next = DSI_DM_WAIT_FOR_START;
							end
							default: begin
								`do_error_handling(1'b1)
							end
						endcase
					end
				end
			end
			
			/*###   SYNC   ######################################################*/
			DSI_SYNC_START: begin
				`if_stop_transmission()
				else begin
					sync.waiting = 1'b1;
					if (((sync.armed == 1'b1) && (sync.fire == 1'b1)) || (sync.armed == 1'b0)) begin
						state_next = DSI_SYNC;
					end
					else begin
						o_busy = 1'b0;
						DSI3_channel_registers_DSI_STAT.SYNC_in = 1'b1;
					end
				end
			end
			
			DSI_SYNC: begin
				`if_stop_transmission()
				else begin
					sync.register = 1'b1;
					sync.channels_to_sync = {command[BIT_EXTERNAL_SYNC],command.data[MSB_CHANNEL_SELECT:LSB_CHANNEL_SELECT]};
					state_next = dsi3_pkg::IDLE;
				end
			end
			
			/*###   Discovery Mode   ######################################################*/
			DSI_DM_WAIT_FOR_START: begin
				mode = MODE_DM;
				`if_stop_transmission()
				else begin
					sync.waiting = 1'b1;
					if (sync.armed == 1'b1) begin
						if (sync.fire == 1'b0) begin
							o_busy = 1'b0;
							DSI3_channel_registers_DSI_STAT.SYNC_in = 1'b1;
						end
					end
					request.request = 1'b1;
					request_acknowledge = request.tick_transmit;
					if (acknowledge == 1'b1)
						state_next = DSI_DM_WAIT;
				end
			end
			
			DSI_DM_WAIT: begin
				mode = MODE_DM;
				if (finished == 1'b1) begin
					state_next = dsi3_pkg::IDLE;
				end
			end
			
			/*###   TDMA packet   ######################################################*/
			DSI_UPLOAD_TDMA_PACKET_EARLIEST: begin
                `if_stop_transmission()
                else begin
    				if (command_reader.empty == 1'b1) begin
    					`do_error_handling(1'b1)
    				end
    				else begin
    					command_reader.action = BUFFER_READ;
    					if (command_reader.ready == 1'b1) begin
    						state_next = DSI_UPLOAD_TDMA_PACKET_LATEST;
                            store_earliest = 1'b1;
    					end
                    end
                end
			end
			
			DSI_UPLOAD_TDMA_PACKET_LATEST: begin
                `if_stop_transmission()
                else begin
    				if (command_reader.empty == 1'b1) begin
    					`do_error_handling(1'b1)
    				end
    				else begin
    					command_reader.action = BUFFER_READ;
    					if (command_reader.ready == 1'b1) begin
    						state_next = DSI_UPLOAD_TDMA_PACKET_INFO;
    						store_latest = 1'b1;
    					end
                    end
                end
			end
			
			DSI_UPLOAD_TDMA_PACKET_INFO :begin
                `if_stop_transmission()
                else begin
    				if (command_reader.empty == 1'b1) begin
    					`do_error_handling(1'b1)
    				end
    				else begin
    					command_reader.action = BUFFER_READ;
    					if (command_reader.ready == 1'b1) begin
    						state_next = DSI_UPLOAD_TDMA_PACKET;
                            store_packet_info = 1'b1;
    					end
                    end
                end
			end
			
			DSI_UPLOAD_TDMA_PACKET : begin
                `if_stop_transmission()
                else begin
    				tdma_writer.action = WRITE_PACKET;
    				if (tdma_writer.acknowledge == 1'b1) begin
    					state_next = dsi3_pkg::IDLE;
                    end
                end
			end
			
			/*###   validate TDMA   ######################################################*/
			DSI_VALIDATE_TDMA_PERIOD : begin
                if (ecc_error_tdma.double_error == 1'b1) begin
                    `do_error_handling(1'b0)
                    state_next = dsi3_pkg::IDLE;
                end
                else begin
                    `if_stop_transmission()
                    else begin
        				if (command_reader.empty == 1'b1) begin
        					`do_error_handling(1'b1)
        				end
        				else begin
        					command_reader.action = BUFFER_READ;
        					if (command_reader.ready == 1'b1) begin
        						state_next = DSI_VALIDATE_WRITE_HEADER;
        						set_period = 1'b1;
                                store_period = 1'b1;
        					end
                        end
                    end
                end
            end
			
			DSI_VALIDATE_WRITE_HEADER: begin
                if (ecc_error_tdma.double_error == 1'b1) begin
                    `do_error_handling(1'b0)
                    state_next = dsi3_pkg::IDLE;
                end
                else begin
                    `if_stop_transmission()
                    else begin
        				tdma_writer.action = WRITE_HEADER;
        				if (tdma_writer.acknowledge == 1'b1) begin
        					state_next = DSI_VALIDATE_TDMA;
                        end
                    end
    			end
			end
			
			DSI_VALIDATE_TDMA : begin
                if (ecc_error_tdma.double_error == 1'b1) begin
                    `do_error_handling(1'b0)
                    state_next = dsi3_pkg::IDLE;
                end
                else begin
                    `if_stop_transmission()
                    else begin
        				tdma_writer.action = VALIDATE;
        				if (tdma_writer.acknowledge == 1'b1) begin
        					state_next = dsi3_pkg::IDLE;
                        end
                    end
                end
			end
			
			/*###   CRM   ######################################################*/
			DSI_CRM_GET_DATA_HIGH: begin
				`if_stop_transmission()
				else begin
					if (command_reader.empty == 1'b1) begin
						`do_error_handling(1'b1)
					end
					else begin
						command_reader.action = BUFFER_READ;
						if (command_reader.ready == 1'b1) begin
							state_next = DSI_CRM_GET_DATA_LOW;
							store_data_high = 1'b1;
						end
					end
				end
			end
			DSI_CRM_GET_DATA_LOW: begin
				`if_stop_transmission()
				else begin
					if (command_reader.empty == 1'b1) begin
						`do_error_handling(1'b1)
					end
					else begin
						command_reader.action = BUFFER_READ;
						if (command_reader.ready == 1'b1) begin
							state_next = DSI_CRM_WAIT_FOR_START;
							store_data_low = 1'b1;
						end
					end
				end
			end
			DSI_CRM_WAIT_FOR_START: begin
				`if_stop_transmission()
				else begin
					sync.waiting = 1'b1;
					if (sync.armed == 1'b1) begin
						if (sync.fire == 1'b0) begin
							o_busy = 1'b0;
							DSI3_channel_registers_DSI_STAT.SYNC_in = 1'b1;
						end
					end
					request.request = 1'b1;
					request_acknowledge = request.tick_transmit;
					if (acknowledge == 1'b1)
						state_next = DSI_CRM_WAIT;
				end
			end
			DSI_CRM_WAIT: begin
				if (finished == 1'b1) begin
					state_next = dsi3_pkg::IDLE;
				end
			end
			
			/*###   WAIT   ######################################################*/
			DSI_READ_WAIT_TIME: begin
                `if_stop_transmission()
                else begin
    				if (command_reader.empty == 1'b1) begin
    					`do_error_handling(1'b1)
    				end
    				else begin
    					command_reader.action = BUFFER_READ;
    					if (command_reader.ready == 1'b1) begin
    						DSI3_channel_registers_WAIT_TIME.TIME_set = 1'b1;
    						DSI3_channel_registers_WAIT_TIME.TIME_in = command_reader_data_corrected[14:0];
    						state_next = DSI_WAITING_WAIT_FOR_START;
    					end
                    end
                end
			end
			DSI_WAITING_WAIT_FOR_START: begin
				`if_stop_transmission()
				else begin
					sync.waiting = 1'b1;
					if (((sync.armed == 1'b1) && (sync.fire == 1'b1)) || (sync.armed == 1'b0)) begin
						state_next = DSI_WAITING;
						start_tick_1us = 1'b1;
					end
					else begin
						o_busy = 1'b0;
						DSI3_channel_registers_DSI_STAT.SYNC_in = 1'b1;
					end
				end
			end
			
			DSI_WAITING: begin
				start_tick_1us = 1'b1;
				`if_stop_transmission(
					DSI3_channel_registers_WAIT_TIME.TIME_set = 1'b1;
					DSI3_channel_registers_WAIT_TIME.TIME_in = '0;
				)
				else begin
					if(tick_1us == 1'b1) begin
						if (DSI3_channel_registers_WAIT_TIME.TIME == '0) begin
							state_next = dsi3_pkg::IDLE;
						end
						else begin
							DSI3_channel_registers_WAIT_TIME.TIME_set = 1'b1;
							DSI3_channel_registers_WAIT_TIME.TIME_in = DSI3_channel_registers_WAIT_TIME.TIME - 15'd1;
						end
					end
				end
			end
			
			/*###   ILOAD   ######################################################*/
            DSI_ILOAD_WAIT_FOR_START: begin
                `if_stop_transmission_iload()
                else begin
                    start_quiescent_current = 1'b1;
                    state_next = DSI_ILOAD_WAIT;
                end
            end
            
            DSI_ILOAD_WAIT: begin
                if (hw_fail_iload == 1'b1) begin
                    `do_error_handling(1'b0)
                end
                else begin
                    if (ready_quiescent_current == 1'b1) begin
                        state_next = dsi3_pkg::IDLE;
                        if ((dsi3_io.rx_idac == '1)) begin
                            set_iq_err = 1'b1;
                        end
                    end
                end
            end
            
			/*###   PDCM   ######################################################*/
			DSI_PDCM_WAIT_FOR_START: begin
				mode = MODE_PDCM;
                if (ecc_error_tdma.double_error == 1'b1) begin
                    `do_error_handling(1'b0)
                    state_next = dsi3_pkg::IDLE;
                end
                else begin
    				`if_stop_transmission()
    				else begin
    					if (tdma_scheme_valid == 1'b0) begin
                            set_pdcm_err = 1'b1;
    						state_next = dsi3_pkg::IDLE;
    					end
    					if ((request.pdcm_period_running == 1'b0) || (sync.armed == 1'b1)) begin
    						sync.waiting = 1'b1;
    					end
    					if (sync.armed == 1'b1) begin
    						if (sync.fire == 1'b0) begin
    							o_busy = 1'b0;
    							DSI3_channel_registers_DSI_STAT.SYNC_in = 1'b1;
    						end
    					end
    					request.request = 1'b1;
    					if (request.tick_pdcm == 1'b1) begin
    						`start_pdcm
    					end
                    end
                end
			end
			DSI_PDCM_WAIT: begin
				pdcm_in_progress_next = 1'b1;
				mode = MODE_PDCM;
                if (ecc_error_tdma.double_error == 1'b1) begin
                    `do_error_handling(1'b0)
                    state_next = dsi3_pkg::IDLE;
                end
                else begin
    				if (finished == 1'b1) begin
    					if (stop_and_clear_buffer == 1'b1) begin
    						state_next = dsi3_pkg::IDLE;
    						periods_next.periods = '0;
    						periods_next.unlimited = 1'b0;
    						stop_and_clear_buffer_next = 1'b0;
    						sync.reset = 1'b1;
    					end
    					else begin
    						if ((periods.periods > 8'd1) || (periods.unlimited == 1'b1)) begin
    							request.request = 1'b1;
    							if ((request.pdcm_period_running == 1'b0) || (request.tick_pdcm == 1'b1))  begin
    								if (request.tick_pdcm == 1'b1) begin
    									`start_pdcm
    									if (acknowledge == 1'b1) begin
    										if (periods.periods != 8'd0) begin
    											periods_next.periods = periods.periods - 8'd1;
    										end
    									end
    								end
    							end
    						end
    						else begin
    							pdcm_in_progress_next = 1'b0;
    							state_next = dsi3_pkg::IDLE;
    						end
    					end
                    end
                end
			end
			default : begin
				`do_error_handling(1'b1)
			end
		endcase
		if (i_transceiver_enable == 1'b0) begin
			state_next = dsi3_pkg::IDLE;
            if (state != dsi3_pkg::IDLE)
                set_com_err = 1'b1;
        end
    end
    
	/*###   command CRC   ######################################################*/
	data_t		crc_data;
	dsi3_crc_parallel i_dsi3_crc_parallel (
		.i_seed(seed    ),
		.i_data(crc_data),
		.o_crc (crc_next));
	
	always_comb begin
		seed = 8'hff;
		if (store_data_low == 1'b1) begin
			seed = crc;
		end
	end
	
	always_comb begin
		crc_data = command_reader_data_corrected;
		if (store_data_low == 1'b1)
			crc_data[7:0] = 8'd0;
	end
	
	always_comb begin
		data_low_crc = data_low;
		if (common_config.crc_enable == 1'b1) begin
			data_low_crc.data[7:0] = crc;
			data_low_crc.ecc       = data_low_crc_ecc;
		end
	end
	
	/*###   DSI3 core   ######################################################*/
	logic	tx, receive_mode_enable;
    `ifdef VCS
    data_t current_time_in_period;
    `endif
	dsi3_core i_dsi3_core (
		.clk_rst                                  (clk_rst                        ),
		.common_config                            (common_config                  ),
		.time_base                                (time_base                      ),
		.pdcm_data_writer                         (pdcm_data_writer               ),
		.crm_data_writer                          (crm_data_writer                ),
        .tdma_reader                              (tdma_reader.master             ),
		.ecc_error_cmd                            (ecc_error_cmd_int.master       ),
		.ecc_error_data                           (ecc_error_data                 ),
		.DSI3_channel_registers_PACKET_STAT       (DSI3_channel_registers_PACKET_STAT.slave),
		.DSI3_channel_registers_FRAME_STAT        (DSI3_channel_registers_FRAME_STAT.slave),
		
		.i_rx                                     (dsi3_io.rx                     ),
		.i_ov                                     (ov_sync                        ),
		.i_uv                                     (uv_sync                        ),
		.i_data_high                              (data_high                      ),
		.i_data_low_crc                           (data_low_crc                   ),
		.i_start                                  (request_acknowledge            ),
		.i_broad_cast                             (broad_cast                     ),
		.i_mode                                   (mode                           ),
		.i_transceiver_enable                     (i_transceiver_enable           ),
		.i_clear_crm_data_buffer                  (i_clear_crm_data_buffer        ),
		.i_clear_pdcm_data_buffer                 (clear_pdcm_data_buffer         ),
		.i_clear_and_invalidate_crm_data_buffer   (i_clear_and_invalidate_crm_data_buffer),
		.i_clear_and_invalidate_pdcm_data_buffer  (i_clear_and_invalidate_pdcm_data_buffer | clear_pdcm_data_buffer_due_to_tdma_error),
		.i_pdcm_receive_timeout                   (request.pdcm_receive_timeout   ),
        .i_stop                                   (stop_transmit_or_receive       ),
		
        `ifdef VCS
        .o_current_time_in_period                 (current_time_in_period         ),
        `endif
		.o_tx                                     (tx                             ),
		.o_transmit_pending                       (o_transmit_pending             ),
		.o_receive_mode_enable                    (receive_mode_enable            ),
		.o_acknowledge_start                      (acknowledge                    ),
		.o_finished                               (finished                       ),
		.o_rx_test                                (tmr_out_dsi.rx_synced          ),
		.o_rx_filtered                            (tmr_out_dsi.rx_filtered        ),
		.o_hw_fail                                (hw_fail_core                   ),
		.o_dm_overflow                            (DSI3_channel_registers_DSI_IRQ_STAT.DMOF_set),
		.o_slaves                                 (DSI3_channel_registers_DSI_STAT.SLAVES_in),
        .o_data_high_ecc_corrected                (DSI3_channel_registers_CRM_WORD1.CRM_WORD1_in),
        .o_data_low_ecc_corrected                 (DSI3_channel_registers_CRM_WORD2.CRM_WORD2_in)
	);
	
	// Register assignments
	assign	DSI3_channel_registers_DSI_CMD.CMD_in = command.command;
	assign	DSI3_channel_registers_DSI_CMD.DATA_in = command.data;
	assign	DSI3_channel_registers_DSI_STAT.PULSECNT_in = periods.periods;
	
	// assign correct trim value according to current RxD value
	assign	dsi3_io.trim_rx1 = (dsi3_io.rx[0] == 1'b1) ? DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.TRIM_REC1 : DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.TRIM_REC1;
	assign	dsi3_io.trim_rx2 = (dsi3_io.rx[1] == 1'b1) ? DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.TRIM_REC2 : DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.TRIM_REC2;
	
	/*###   quiescent current   #########################################*/
    logic   rx_i_q_sync;
    sync i_sync_rx_iq (
        .clk_rst   (clk_rst     ),
        .i_in      (dsi3_io.i_q ),
        .o_test_out(tmr_out_dsi.icmp_synced),
        .o_out     (rx_i_q_sync )
    );
    
    dsi3_iload_control i_dsi3_iload_control (
        .DSI_LOAD      (DSI3_channel_registers_DSI_LOAD.slave),
        .clk_rst       (clk_rst                 ),
        .i_rx_iload_cmp(rx_i_q_sync             ),
        .i_start       (start_quiescent_current ),
        .i_tick_1us    (time_base.tick_1us      ),
        .o_ready       (ready_quiescent_current ),
        .o_hw_fail     (hw_fail_iload           )
    );
    
    assign  dsi3_io.rx_idac = DSI3_channel_registers_DSI_LOAD.LOAD;
    
    
	/*###   TDMA   ######################################################*/
	tdma_manager #(.BASE_ADDRESS(BASE_ADDR_TDMA)) i_tdma_manager (
		.clk_rst                 (clk_rst			                        ),
		.elip                    (elip_tdma                                 ),
		.writer	                 (tdma_writer.slave	                        ),
        .reader                  (tdma_reader.slave                         ),
        .ecc_error               (ecc_error_tdma                            ),
		.i_period                (DSI3_channel_registers_PDCM_PERIOD.PDCMPER),
        .i_invalidate_tdma_scheme(i_invalidate_tdma_scheme                  ),
        `ifdef VCS
        .i_tick_1us              (time_base.tick_1us                        ),
        .i_current_time_in_period(current_time_in_period                    ),
        `endif
		.o_tdma_scheme_valid     (tdma_scheme_valid                         ),
        .o_tdma_frame_word_count (o_tdma_frame_word_count                   ),
        .o_hw_fail               (hw_fail_tdma_manager                      ),
        .o_clear_data_buffer     (clear_pdcm_data_buffer_due_to_tdma_error  )
    );
	
	assign	o_no_tdma_scheme_defined = ~tdma_scheme_valid;
    
	assign	tdma_writer.packet_index = tdma_header.packet_count;
	assign	tdma_writer.packet = tdma_packet;
	assign	tdma_writer.header = tdma_header;
	
	/*###   test   ######################################################*/
	logic	tx_sel_val;
	logic	tmr_dig_prevent_deactivation;
	test_dsi #(
		.BASE_ADDR (BASE_ADDR_TEST),
		.ADDR_WIDTH(JTAG_IR_WIDTH )
	) i_test_dsi (
		.jtag_bus                      (jtag_bus                    ),
		.o_jtag_dr                     (o_jtag_dr                   ),
		.tmr_dsi                       (tmr_dsi                     ),
		.i_tx_tmr_in                   (tx_sel_val                  ),
		.o_tx_tmr_in                   (dsi3_io.tx                  ),
		.i_TX_tmr_val                  (tx                          ),
		.o_TX_tmr_val                  (tx_sel_val                  ),
		.i_RX_TXN_tmr_val              (receive_mode_enable         ),
		.o_RX_TXN_tmr_val              (dsi3_io.receive_mode_enable ),
		.i_RX_ON_tmr_val               (i_transceiver_enable        ),
		.o_RX_ON_tmr_val               (dsi3_io.rx_on               ),
		.i_TX_ON_tmr_val               (i_transceiver_enable        ),
		.o_TX_ON_tmr_val               (dsi3_io.tx_on               ),
		.i_HVCASC_ON_tmr_val           (i_transceiver_enable        ),
		.o_HVCASC_ON_tmr_val           (dsi3_io.tx_hvcasc_on        ),
		.o_tmr_dig_PREVENT_DEACTIVATION(tmr_dig_prevent_deactivation));
	
	sync i_sync_tmr_dig_prevent_deactivation (
		.clk_rst   (clk_rst                       ),
		.i_in      (tmr_dig_prevent_deactivation  ),
		.o_test_out(                              ),
		.o_out     (o_tmr_dig_prevent_deactivation));
	
	assign	tmr_out_dsi.ov = dsi3_io.ov;
	assign	tmr_out_dsi.uv = dsi3_io.uv;
	assign	tmr_out_dsi.rx = dsi3_io.rx;
	assign	tmr_out_dsi.icmp = dsi3_io.i_q;
	
endmodule