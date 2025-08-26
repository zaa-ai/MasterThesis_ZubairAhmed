module ANA #(
		parameter DSI3_COUNT = 2
	)( 
		/* input reals */
		input 	real 		VSUP,
		input 	real		GND,
		input	real		DGND,
		
		/*input logics*/
		input	logic[DSI3_COUNT*dsi3_pkg::DSI3_TX_DAC_WIDTH-1:0]		DSI3_TX,
		input   logic       REG_VDD18_DIS,
		input   logic[1:0]	TRIM_OT,
		input	logic		OTP_EHV_1V8,
		input	logic[DSI3_COUNT-1:0]	DSI_RX_TXN, 
		input	logic[(DSI3_COUNT*2)-1:0]	DSI_TX_CFG,
		input	logic[(DSI3_COUNT*5)-1:0]	DSI_RX_DAC,
		input	logic[DSI3_COUNT-1:0]	DSI_RX_ON,
		input	logic[DSI3_COUNT-1:0]	DSI_RX_FILTER_FAST,
		input	logic[DSI3_COUNT-1:0]	DSI_TX_ON,
		input	logic[DSI3_COUNT-1:0]	DSI_TX_HVCASC_ON,
		input	logic		LDO_EN,
		input	logic[2:0]	LDO_CTRL,
		input	logic[(DSI3_COUNT*3)-1:0]	VDSI_CTRL,
		input	logic		A_OTP_VRR,
		
		/* output reals */
		output	real		DSI[DSI3_COUNT-1:0],
		output	real		VDD18,
		output 	real 		VCC,
		output	real		AOUT,
		output	real		LDO,
		
		/*output logics*/
		output	logic		O_PORB,
		output	logic[DSI3_COUNT-1:0] DSI3_REC1,
		output	logic[DSI3_COUNT-1:0] DSI3_REC2,
		
		output	logic		VCC_OK,
		output  logic[DSI3_COUNT-1 : 0] DSI_OV,
		output  logic[DSI3_COUNT-1 : 0] DSI_UVB,
		output  logic[DSI3_COUNT-1 : 0] DSI3_ILOAD_CMP,
		output	logic		A_OTP_EHV,
		output	logic		OT_ERROR,
		output	logic		OT_WARN,
		output	logic		LDO_OK,
		output	logic		VRR_OK
	);
	
	/*###   DSI channels   ######################################################*/
	import dsi3_pkg::*;
	
	// @SuppressProblem -type fully_non_driven_static_variable -count 1 -length 1
	// @SuppressProblem -type fully_unread_static_variable -count 1 -length 1
	dsi3_pkg::dsi3_rx_dac_t	dsi3_rx_dac[DSI3_COUNT-1:0];
	dsi3_pkg::dsi3_tx_dac_t	dsi3_txd[DSI3_COUNT-1:0];
	// @SuppressProblem -type fully_non_driven_static_variable -count 1 -length 1
	// @SuppressProblem -type fully_unread_static_variable -count 1 -length 1
	logic [1:0] dsi3_rxd[DSI3_COUNT-1:0];
	
	generate
		for (genvar i=0; i<DSI3_COUNT; i++) begin :	gen_dsi_trx
			
			assign dsi3_txd[i] = DSI3_TX[((i+1)*DSI3_TX_DAC_WIDTH-1)-:DSI3_TX_DAC_WIDTH];
			
			dsi_transceiver i_dsi_transceiver (
				.I_DSI3_TX            (dsi3_txd[i]            ), 
				.VDSI				  (LDO					  ),
				.DSI_RX_TXN           (DSI_RX_TXN[i]          ), 
				.DSI_TX_CFG           (DSI_TX_CFG[((i+1)*2)-1-:2]), 
				.DSI_RX_ON            (DSI_RX_ON[i]           ), 
				.DSI_RX_FILTER_FAST   (DSI_RX_FILTER_FAST[i]  ), 
				.DSI_TX_ON            (DSI_TX_ON[i]           ), 
				.DSI_TX_HVCASC_ON     (DSI_TX_HVCASC_ON[i]    ), 
				.DSI3_REC1            (DSI3_REC1[i]           ), 
				.DSI3_REC2            (DSI3_REC2[i]           ), 
				.VDSI_UVB             (DSI_UVB[i]              ), 
				.VDSI_OV              (DSI_OV[i]              ), 
				.DSI                  (DSI[i]                 ),
				.VDSI_CTRL            (VDSI_CTRL[((i+1)*3)-1-:3]),
                .I_DSI_RX_DAC         (DSI_RX_DAC[((i+1)*5)-1-:5]),
                .DSI3_ILOAD_CMP       (DSI3_ILOAD_CMP[i]       )
            );
			
		end			
	endgenerate
	
	/*###   LDO Regulator   ######################################################*/
	real	LDO_target;
	always_comb begin
		LDO_target = 5.6+(0.7*int'(LDO_CTRL));
	end
	
	always@(*) begin
		if (LDO_EN == 1'b1) begin
			if ((VSUP - 0.7) > LDO_target) begin
				LDO = LDO_target;
			end
			else begin
				if (VSUP > 0.7)	begin
					LDO = VSUP - 0.7;
				end
				else begin
					LDO = 0.0;
				end
			end
		end
		else begin
			LDO = 0.0;
		end
	end
	
	initial LDO_OK = 1'b0;
	always@(*) begin
		if (LDO_EN == 1'b1) begin
			if (LDO_OK == 1'b1) begin
				if (LDO < 0.8*LDO_target) begin
					LDO_OK = 1'b0;
				end
			end
			else begin
				if (LDO > 0.9*LDO_target) begin
					LDO_OK = 1'b1;
				end
			end
		end
		else
			LDO_OK = 1'b0;
	end
	
	/*###   VRR monitor   ######################################################*/
	always@(A_OTP_VRR) begin
		if (A_OTP_VRR === 1'b1) begin
			VRR_OK = 1'b1;
		end
		else begin
			VRR_OK = 1'b0;
		end
	end
	
	/*###   Temperature monitor   ######################################################*/
	initial begin
		OT_ERROR = 1'b0;
		OT_WARN = 1'b0;
	end
	
	real	temperature;	// set from outside
	always@(*) begin
		if (OT_ERROR) begin
			if (temperature < $itor(155+5*int'(TRIM_OT))) begin
				OT_ERROR = 1'b0;
			end
		end
		else begin
			if (temperature > $itor(165+5*int'(TRIM_OT))) begin
				OT_ERROR = 1'b1;
			end
		end
		if (OT_WARN) begin
			if (temperature < $itor(115+5*int'(TRIM_OT))) begin
				OT_WARN = 1'b0;
			end
		end
		else begin
			if (temperature > $itor(125+5*int'(TRIM_OT))) begin
				OT_WARN = 1'b1;
			end
		end
	end
	
	assign AOUT = 0.0;
	
	supply_top i_supply (
			.VCC       (VCC      ), 
			.AGND      (GND      ), 
			.VDD1V8     (VDD18   ),
			.VDD1V8_sense(VDD18),
			.REG_DIS   (REG_VDD18_DIS),
			.PORB      (O_PORB   ),
			.VCC_OK	   (VCC_OK   ),
			.VSUP      (VSUP)
		);
	
	assign A_OTP_EHV = OTP_EHV_1V8;
	
	always@(DGND) begin
		if (DGND != 0.0) begin
			$fatal("DGND is not 0.0. DGND=%f", DGND);
		end
	end
	
endmodule
