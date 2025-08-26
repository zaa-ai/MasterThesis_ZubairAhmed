/**
 * Module: dsi_transceiver
 * 
 * DSI Transceiver model
 */
module dsi_transceiver #(
		parameter DSI3_RX_DAC_WIDTH = 5
	) (
		input	logic[dsi3_pkg::DSI3_TX_DAC_WIDTH-1:0]		I_DSI3_TX,
		input	real 	VDSI,
        input   logic[DSI3_RX_DAC_WIDTH-1:0]	I_DSI_RX_DAC,
		
		input	logic	DSI_RX_TXN, 
		input	logic[1:0]	DSI_TX_CFG,
		input	logic	DSI_RX_ON,
		input	logic	DSI_RX_FILTER_FAST,
		input	logic	DSI_TX_ON,
		input	logic	DSI_TX_HVCASC_ON,
		input	logic[2:0]	VDSI_CTRL,
		
		output	logic	DSI3_REC1,
		output	logic	DSI3_REC2,
		output	logic	DSI3_ILOAD_CMP,
		output	logic	VDSI_OV,
		output	logic	VDSI_UVB,
		output	real	DSI
	);
	
	/*###   Quiescent current regulation   ######################################################*/
	real	iload;
	real	iload_target;
	assign	iload_target = (I_DSI_RX_DAC) * 0.145;
//	assign	iload_target = 0.5; 
	real i_rec;
	real i_transmit;
	assign	i_rec = (iload - iload_target + i_transmit);
	real i_rec_th[1:0];
	assign	i_rec_th[0] = 9.0;
	assign	i_rec_th[1] = 18.0;
	
	bit i_rec_gt_0;
	assign i_rec_gt_0 = (i_rec > 0.0) ? 1'b1 : 1'b0;
	
        always@(*) begin
		if (DSI_RX_ON == 1'b1) begin
			if (i_rec_gt_0 == 1'b1) begin
				fork
					#400ns DSI3_ILOAD_CMP = 1'b1;
					@(negedge i_rec_gt_0);
				join_any
				disable fork;
			end
			else begin
				fork
					#1000ns DSI3_ILOAD_CMP = 1'b0;
					@(negedge i_rec_gt_0);
				join_any
				disable fork;
			end
		end
		else begin
			DSI3_ILOAD_CMP = 1'b0;
		end
	end

	/*###   receiver   ######################################################*/
	always_comb begin
		DSI3_REC1 = 1'b0;
		DSI3_REC2 = 1'b0;
		if (DSI_RX_ON == 1'b1) begin
			if (i_rec > i_rec_th[0]) begin
				DSI3_REC1 = 1'b1;
			end
			if (i_rec > i_rec_th[1]) begin
				DSI3_REC2 = 1'b1;
			end
		end
	end
	
	/*###   DSI voltage   ######################################################*/
	real	DSI_target;
	always_comb begin
		DSI_target = 4.5+(0.7*int'(VDSI_CTRL));
	end
	
	/*###   DSI voltage monitor   ######################################################*/
	always_comb begin	
		if (DSI < DSI_target * 0.55) begin
			VDSI_UVB = 1'b0;
		end
		else begin
			VDSI_UVB = 1'b1;
		end
	end
	
	always_comb begin	
		if (DSI < DSI_target * 1.35) begin
			VDSI_OV = 1'b0;
		end
		else begin
			VDSI_OV = 1'b1;
		end
	end
	
	/*###   Transceiver   ######################################################*/
	bit unload_DSI;
	real DSI_for_unload;
	always_comb begin
		unload_DSI = 1'b0;
		if ((DSI_TX_ON == 1'b1) && (DSI_TX_HVCASC_ON == 1'b1)) begin
			if (DSI_RX_TXN == 1'b1) begin
				DSI = VDSI-1.1;
			end
			else begin
				DSI = VDSI-1.1 - 2.0 + (2.0/31.0*(I_DSI3_TX));
			end
		end
		else begin
			unload_DSI = 1'b1;
			DSI = DSI_for_unload;
		end
	end
	
	always@(unload_DSI, DSI_for_unload) begin
		if (unload_DSI) begin
			fork
				unload_dsi_();
			join_none
		end
		else begin
			DSI_for_unload = DSI;
		end
	end
	
	task unload_dsi_();
		fork
			begin
				while (DSI_for_unload > 0) begin
					#1us DSI_for_unload -= 0.1;
				end
				DSI_for_unload = 0.0;
			end
			begin
				@(negedge unload_DSI);
			end
		join_any
		disable fork;
	endtask
	
	realtime last_time;
	real	last_dsi;
	event	time_out, dsi_event;
	bit		first_time = 1'b1;
	
	always@(DSI) begin
		if (!first_time)	begin
			set_current(get_current(DSI, last_dsi, last_time));
			-> dsi_event;
		end
		else begin
			first_time = 1'b0;
		end
		last_time = $time;
		last_dsi = DSI;
	end
	
	always@(time_out) begin
		i_transmit = 0.0;
		first_time = 1'b1;
	end
	
	initial begin
		forever begin
			@(negedge first_time);
			while (!first_time) begin
				fork
					begin
						#1;
						@(dsi_event);
					end
					begin
						#1us;
						->time_out;
					end
				join_any
				disable fork;
			end
		end
	end
	
	task set_current(real current);
		i_transmit = 1000*current;
	endtask
	
	function automatic real get_current(real current_dsi, real last_dsi, realtime last_time);
		real temp;
		temp = 40e-9*(current_dsi - last_dsi)/(($realtime - last_time)/1.0s); // i = C * dU/dt
		return temp;
	endfunction

endmodule
