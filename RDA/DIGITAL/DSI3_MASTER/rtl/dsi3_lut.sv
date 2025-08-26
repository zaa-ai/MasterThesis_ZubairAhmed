/*
 * This LUT was tested in EME labratory with 52143
 * Since transmitter lacks bandwidth, it is not fast enough to follow 18MHz wave shape DAC. As result the rising and falling edges differ. 
 * 0 FALL
 * 1 RISE
 * Peak of fundamental can not be omitted. Overtones are defined by shape of curve not by bit time. Therefore a scaling of LUT with bit time is not needed.
 * A simple up/down counter controlled by tx is sufficient. tx can control LUT slice also.  
 */
logic [DSI3_TX_DAC_WIDTH-1:0] LUT [0:1] [0:71];
assign LUT[0][0:71] = {5'd31, 5'd31, 5'd31, 5'd31, 5'd31, 5'd31, 5'd31, 5'd31, 5'd31, 5'd30, 5'd30, 5'd29, 5'd29, 5'd29, 5'd28, 5'd28, 5'd27, 5'd27, 5'd26, 5'd26, 5'd25, 5'd25, 5'd24, 5'd24, 5'd23, 5'd22, 5'd22, 5'd21, 5'd21, 5'd20, 5'd19, 5'd19, 5'd18, 5'd17, 5'd17, 5'd16, 5'd15, 5'd14, 5'd14, 5'd13, 5'd12, 5'd12, 5'd11, 5'd10, 5'd10, 5'd9, 5'd9, 5'd8, 5'd7, 5'd7, 5'd6, 5'd6, 5'd5, 5'd5, 5'd4, 5'd4, 5'd3, 5'd3, 5'd2, 5'd2, 5'd2, 5'd1, 5'd1, 5'd1, 5'd1, 5'd1, 5'd0, 5'd0, 5'd0, 5'd0, 5'd0, 5'd0};
assign LUT[1][0:71] = {5'd31, 5'd31, 5'd31, 5'd30, 5'd30, 5'd30, 5'd30, 5'd30, 5'd29, 5'd29, 5'd29, 5'd28, 5'd28, 5'd28, 5'd27, 5'd27, 5'd26, 5'd26, 5'd26, 5'd25, 5'd25, 5'd24, 5'd24, 5'd23, 5'd23, 5'd22, 5'd21, 5'd21, 5'd20, 5'd20, 5'd19, 5'd19, 5'd18, 5'd17, 5'd17, 5'd16, 5'd16, 5'd15, 5'd14, 5'd14, 5'd13, 5'd12, 5'd12, 5'd11, 5'd11, 5'd10, 5'd10, 5'd9, 5'd8, 5'd8, 5'd7, 5'd7, 5'd6, 5'd6, 5'd5, 5'd5, 5'd5, 5'd4, 5'd4, 5'd3, 5'd3, 5'd3, 5'd2, 5'd2, 5'd2, 5'd1, 5'd1, 5'd1, 5'd1, 5'd1, 5'd0, 5'd0};

