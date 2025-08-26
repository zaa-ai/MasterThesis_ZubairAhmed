//this is a TAP master for ieee 1149.1
module tapm #(
		parameter ir_length = 8,
		parameter dr_length = 28
		)(
		input logic rstn, clk, // low active reset, clock
		input logic tick, soc, // tick for tck scaling
		output logic eoc, // request was done, use handshake with soc
		input logic [7:0] ir, //instruction to send lsb first, maybe latched, shall be fix until eoc = 1
		input logic [27:0] dr,//data to send lsb first, maybe latched
		output logic tms, tck, tdi, trstn  //tms is set with posedge tck, tdi is set with negedge of tck
		//	input logic tdo, //not supported now
		//	output logic [15:0] foo //not supported now
		);

	//define states for master TAP
	//do not support PAUSE_DR EXIT2_DR PAUSE_IR EXIT2_IR
	typedef enum { POR, TEST_LOGIC_RESET, RUN_TEST_IDLE, SELECT_DR_SCAN, CAPTURE_DR, SHIFT_DR, EXIT1_DR, UPDATE_DR, SELECT_DR_IR_SCAN, SELECT_IR_SCAN, CAPTURE_IR, SHIFT_IR, EXIT1_IR, UPDATE_IR} t_tap;
	//statemachine signals
	t_tap cs, ns;
	//bit selection for ir and dr
	logic [4:0] sel;

	//make TCK
	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			tck <= '0;
		end else begin
			if (tick) tck <= ~ tck;
		end
	end
	//FSM
	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			cs <= POR;
		end else begin
			if (tick &! tck) cs <= ns;
		end
	end

	//next state stuff
	always_comb begin
		ns <= cs;
		case (cs)
			POR : 			    ns <= TEST_LOGIC_RESET;
			TEST_LOGIC_RESET :	if (!tms)
					ns <= RUN_TEST_IDLE; //may be extended to 6 TMS=H
			RUN_TEST_IDLE : if (tms)
					ns <= SELECT_DR_IR_SCAN;
			SELECT_DR_IR_SCAN :	ns <= SELECT_IR_SCAN;
			SELECT_IR_SCAN :	ns <= CAPTURE_IR;
			CAPTURE_IR	 :	ns <= SHIFT_IR;
			SHIFT_IR :	if (sel == (ir_length-1))
					ns <= EXIT1_IR;
			EXIT1_IR 	:	ns <= UPDATE_IR;
			UPDATE_IR :		ns <= SELECT_DR_SCAN;
			SELECT_DR_SCAN :	ns <= CAPTURE_DR;
			CAPTURE_DR :		ns <= SHIFT_DR;
			SHIFT_DR :	if (sel == (dr_length-1))
					ns <= EXIT1_DR;
			EXIT1_DR 	:	ns <= UPDATE_DR;
			UPDATE_DR 	:	ns <= RUN_TEST_IDLE;
			default : ns <= TEST_LOGIC_RESET;
		endcase
	end

	//TMS & shall be sampled on rising edge of TCK , 4.3.1 & 4.4.1 -> we set it on falling edge
	//tms coding
	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			tms <= '0;
		end else begin
			if (tick & tck) begin
				tms <= '0;
				case (cs)
					TEST_LOGIC_RESET : if (sel < 5) begin tms <= '1; end else begin tms <= '0; end
					RUN_TEST_IDLE :	if(soc)	tms <= '1;
					SELECT_DR_IR_SCAN :	tms <= '1;
					SHIFT_IR : if (sel == (ir_length - 1)) tms <= '1;
					EXIT1_IR :		tms <= '1;
					UPDATE_IR :		tms <= '1;
					SHIFT_DR :  if (sel == (dr_length -1 )) tms <= '1;
					EXIT1_DR :		tms <= '1;
				endcase
			end
		end
	end

	//bit section + tdi
	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			sel <= '0;
			//			tdi <= '0;
		end else begin
			if (tick &! tck) begin
				case (cs)
					TEST_LOGIC_RESET : sel <= sel + 1;
					RUN_TEST_IDLE : sel <= '0;
					CAPTURE_IR : sel <= '0;
					CAPTURE_DR : sel <= '0;
					SHIFT_IR : begin
						//						tdi <= ir[sel];
						sel <= sel + 1;
					end
					SHIFT_DR : begin
						//						tdi <= dr[sel];
						sel <= sel + 1;
					end
				endcase
			end
		end
	end
	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			//			sel <= '0;
			tdi <= '0;
		end else begin
			if (tick & tck) begin
				case (cs)
					//					CAPTURE_IR : sel <= '0;
					//					CAPTURE_DR : sel <= '0;
					SHIFT_IR : begin
						tdi <= ir[sel];
						//						sel <= sel + 1;
					end
					SHIFT_DR : begin
						tdi <= dr[sel];
						//						sel <= sel + 1;
					end
				endcase
			end
		end
	end

	//end
	always_comb begin
		case (cs)
			RUN_TEST_IDLE : eoc <= '1;
			default :  eoc <= '0;
		endcase
	end
	//end
	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			trstn <= '0;
		end else begin
			if (tick & tck) begin
				case (cs)
					POR	 : trstn <= '0;
					default :  trstn <= '1;
				endcase
			end
		end
	end

endmodule
