//control TAP master
module dojtag (
		input logic rstn, clk, // low active reset, clock
		input logic soc, tick,
		output logic eoc, // request was done, use handshake with soc
		output logic tms, tck, tdi, trstn
		);

	//define IR+DR
	`include "dojtag_inc.sv"

	//select mem via sel
	logic [0:0] sel;
	// 
	logic tap_eoc, tap_soc;
	t_irdr irdr;

	//use FSM for CTRL
	typedef enum {POR, IDLE, SOC, EOC} t_fsm;
	t_fsm cs, ns;

	//IDLE -soc-> SOC -> EOC -nr-> SOC|IDLE
	//FSM
	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			cs <= POR;
		end else begin
			cs <= ns;
		end
	end
	//next state stuff
	always_comb begin
		ns <= cs;
		case (cs)
			POR	 : if ( tap_eoc) ns <= IDLE;
			IDLE : if ( soc    ) ns <= SOC;
			SOC	 : if (!tap_eoc) ns <= EOC;
			EOC	 : if ( tap_eoc) begin
					if (sel == 0)
						ns <= IDLE;
					else
						ns <= SOC;
				end
			default : ns <= IDLE;
		endcase
	end
	//soc & eocs
	always_comb begin
		eoc	<= '0;
		tap_soc	<= '0;
		case (cs)
			IDLE	: eoc	<= '1;
			SOC	: tap_soc	<= '1;
		endcase
	end

	always_ff @(negedge rstn or posedge clk iff rstn)
	begin
		if (!rstn) begin
			sel <= '1;
		end else begin
			case (cs)
				IDLE	: sel <= '1;
				EOC	: if (tap_eoc) begin
						sel <= sel - 1;
					end
			endcase
		end
	end
	//Is this synthesis able?
	assign irdr = mem[sel];

	tapm tapm_inst (.soc(tap_soc), .eoc(tap_eoc), .ir(irdr.ir), .dr(irdr.dr), .*);

endmodule
