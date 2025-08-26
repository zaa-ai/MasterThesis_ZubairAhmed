`ifndef DSI3_PKG
	`define DSI3_PKG
	/**
	 * Package: dsi3_pkg
	 *
	 * Package including all stuff needed for DSI3, e.g. CRC calc functions, type definitions, LUTs
	 */
	package dsi3_pkg;

		localparam	DSI3_TX_DAC_WIDTH = 5;
		localparam	DSI3_TX_TBIT_CFG_WIDTH = 2;
		localparam	DSI3_RX_DAC_WIDTH = 5;
		localparam	DSI3_RX_TRIM_WIDTH = 4;
		localparam	DSI_OC_DEB_TIME	= 3;	// ms
		
		typedef	enum logic[1:0] {C0=2'd0, C1=2'd1, C2=2'd2, CX=2'd3} dsi3_chip;
		typedef	dsi3_chip[2:0]	dsi3_symbol;
		typedef	logic[DSI3_TX_DAC_WIDTH-1:0]		dsi3_tx_dac_t;
		typedef	logic[DSI3_TX_TBIT_CFG_WIDTH-1:0]	dsi3_tx_tbit_t;
		typedef	logic[DSI3_RX_DAC_WIDTH-1:0]		dsi3_rx_dac_t;
		typedef logic[DSI3_RX_TRIM_WIDTH-1:0]		dsi3_rx_trim_t;
		typedef	logic[7:0]							dsi3_crc_t;
		typedef logic[3:0]							dsi3_filter_counter_t;

		typedef logic[3:0]	transmit_time_count_t;
		localparam	transmit_time_count_t	TRANSMIT_MODE_ENABLE_TIME = transmit_time_count_t'(3);
		localparam	transmit_time_count_t	TRANSMIT_MODE_DISABLE_TIME = transmit_time_count_t'(1);
		
		typedef logic[20:0] period_counter_t;	// 5 Bits more than period value size for system clocking of period register

		typedef enum logic [4:0] {
			IDLE,
			DECODE,
			DSI_CRM_GET_DATA_HIGH,
			DSI_CRM_GET_DATA_LOW,
			DSI_CRM_WAIT_FOR_START,
			DSI_CRM_START,
			DSI_CRM_WAIT,
			DSI_UPLOAD_TDMA_PACKET,
			DSI_UPLOAD_TDMA_PACKET_EARLIEST,
			DSI_UPLOAD_TDMA_PACKET_LATEST,
			DSI_UPLOAD_TDMA_PACKET_INFO,
			DSI_VALIDATE_TDMA_PERIOD,
			DSI_VALIDATE_WRITE_HEADER,
			DSI_VALIDATE_TDMA,
			DSI_PDCM_SEND,
			DSI_PDCM_WAIT_FOR_START,
			DSI_PDCM_WAIT,
			DSI_READ_WAIT_TIME,
			DSI_WAITING,
			DSI_WAITING_WAIT_FOR_START,
			DSI_SYNC_START,
			DSI_SYNC,
			DSI_DM_WAIT_FOR_START,
			DSI_DM_WAIT,
            DSI_ILOAD_WAIT_FOR_START,
            DSI_ILOAD_WAIT
		} dsi_command_control_state_e;

		typedef enum logic[1:0]{
			SID_0Bit = 2'b00,
			SID_4Bit = 2'b01,
			SID_8Bit = 2'b10,
			SID_16Bit_CRC = 2'b11
		} sid_length_e;
        
        localparam  logic[15:0] SEED_8Bit_CRC = 16'h00ff;
        localparam  logic[15:0] SEED_16Bit_CRC = 16'hffff;

		localparam	logic[8:0]	TIME_TO_START_TRANSMITTER = 9'(TRANSMIT_MODE_ENABLE_TIME + transmit_time_count_t'(1));

		typedef enum logic[1:0] {BITTIME_8US=2'd0, BITTIME_16US=2'd1, BITTIME_32US=2'd2, BITTIME_UNUSED=2'd3} dsi3_bit_time_e;
		
		typedef enum logic[1:0] {CHIPTIME_2US=2'd0, CHIPTIME_3US=2'd1, CHIPTIME_4US=2'd2, CHIPTIME_5US=2'd3} dsi3_chip_time_e;

		typedef enum logic[1:0] {MODE_PDCM=2'b00, MODE_CRM=2'b01, MODE_DM=2'b11} channel_mode_t;
		
		function automatic int unsigned get_bit_time_factor(dsi3_bit_time_e bit_time);
			case (bit_time)
				BITTIME_8US, BITTIME_16US, BITTIME_32US: return (1<<bit_time);
				default : return 1;
			endcase
		endfunction
		
		function automatic int unsigned get_bit_time_shift(dsi3_bit_time_e bit_time);
			case (bit_time)
				BITTIME_8US, BITTIME_16US, BITTIME_32US: return int'(bit_time);
				default : return int'(BITTIME_8US);
			endcase
		endfunction

		function automatic int get_bit_time(dsi3_bit_time_e bit_time);
			case (bit_time)
				BITTIME_8US: return 8;
				BITTIME_16US: return 16;
				BITTIME_32US: return 32;
				default : return 0;
			endcase
		endfunction


		`ifdef VCS

			typedef	enum int {DM=0, PDCM=1, CRM=32, UNKNOWN} dsi3_msg_type;

			function dsi3_msg_type get_master_message_type_from_length(int length);
				dsi3_msg_type temp;
				case (length)
					 0 : temp = DM;
					 1 : temp = PDCM;
					32 : temp = CRM;
					default: temp = UNKNOWN;
				endcase
				return temp;
			endfunction

			const dsi3_symbol dsi3_symbol_lut[int]='{
					'h0: dsi3_symbol'({C1, C1, C0}),
					'h1: dsi3_symbol'({C2, C1, C1}),
					'h2: dsi3_symbol'({C1, C0, C2}),
					'h3: dsi3_symbol'({C2, C0, C2}),
					'h4: dsi3_symbol'({C1, C0, C0}),
					'h5: dsi3_symbol'({C2, C1, C2}),
					'h6: dsi3_symbol'({C1, C1, C2}),
					'h7: dsi3_symbol'({C2, C0, C1}),
					'h8: dsi3_symbol'({C2, C2, C0}),
					'h9: dsi3_symbol'({C2, C1, C0}),
					'ha: dsi3_symbol'({C1, C2, C2}),
					'hb: dsi3_symbol'({C2, C2, C1}),
					'hc: dsi3_symbol'({C1, C2, C0}),
					'hd: dsi3_symbol'({C2, C0, C0}),
					'he: dsi3_symbol'({C1, C0, C1}),
					'hf: dsi3_symbol'({C1, C2, C1})
				};

			function logic[3:0] get_symbol(input dsi3_symbol symbol);
				case (symbol)
					dsi3_symbol'({C1, C1, C0}):	return 4'h0;
					dsi3_symbol'({C2, C1, C1}):	return 4'h1;
					dsi3_symbol'({C1, C0, C2}):	return 4'h2;
					dsi3_symbol'({C2, C0, C2}):	return 4'h3;
					dsi3_symbol'({C1, C0, C0}):	return 4'h4;
					dsi3_symbol'({C2, C1, C2}):	return 4'h5;
					dsi3_symbol'({C1, C1, C2}):	return 4'h6;
					dsi3_symbol'({C2, C0, C1}):	return 4'h7;
					dsi3_symbol'({C2, C2, C0}):	return 4'h8;
					dsi3_symbol'({C2, C1, C0}):	return 4'h9;
					dsi3_symbol'({C1, C2, C2}):	return 4'ha;
					dsi3_symbol'({C2, C2, C1}):	return 4'hb;
					dsi3_symbol'({C1, C2, C0}):	return 4'hc;
					dsi3_symbol'({C2, C0, C0}):	return 4'hd;
					dsi3_symbol'({C1, C0, C1}):	return 4'he;
					dsi3_symbol'({C1, C2, C1}):	return 4'hf;
					default: begin
						return 4'hx;
					end
				endcase
			endfunction

			/*###   Cable modeling   ######################################################*/
			typedef struct {
				logic	Voltage;
				int		Current;
			} dsi3_wire;

			typedef struct {
				real v;
				real i;
				logic active_v;
				logic active_i;
			} dsi3_cable;

			function automatic dsi3_cable dsi3_cable_rf(input dsi3_cable driver[]);
				// ToDo: r=0 --> div durch 0!
				int count_v = 0;
				real vs = 0.0;
				real is = 0.0;
				dsi3_cable_rf.v = 0.0;
				dsi3_cable_rf.i = 0.0;
				dsi3_cable_rf.active_v = 1'b0;
				dsi3_cable_rf.active_i = 1'b0;
				if (driver.size == 1) begin // for changing the value of a single net
					dsi3_cable_rf = driver[0];
				end else begin
					foreach (driver[i]) begin
						if (driver[i].active_v) begin
							vs += driver[i].v;
							count_v++;
						end
						if (driver[i].active_i) begin
							is += driver[i].i;
						end
					end
					if (count_v > 0) begin
						dsi3_cable_rf.active_v = 1'b1;
						dsi3_cable_rf.v = vs/count_v;
					end
					if (count_v > 0) begin
						dsi3_cable_rf.active_i = 1'b1;
						dsi3_cable_rf.i = is;
					end

				end
			endfunction

			//nettype dsi3_cable dsi3_cable_nt with dsi3_cable_rf;

		`endif



	endpackage

`endif
