module clk_gate(ECK, CK, E, SE);

output ECK; 
input  CK; 
input  E;
input  SE;

pure_tlatx3 i_pure_tlatx3 (.ECK(ECK), .CK(CK), .E(E), .SE(SE));

endmodule
