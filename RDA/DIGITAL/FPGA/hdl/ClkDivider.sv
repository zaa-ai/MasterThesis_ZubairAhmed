`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 17.03.2017 13:18:50
// Design Name: 
// Module Name: ClkDivider
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: Clock divider
// Aus 10 MHz mach 500 kHz für reference clock REFC
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module ClkDivider(
    input clk,
    output logic clk_div
    );
    
    localparam constantNumber = 10;
    logic [3:0] count;

// for fpga designs Xilinx recomends to work without resets...     
    always @ (posedge(clk))
    begin
    	if (count == constantNumber - 1)
            count <= 3'b0;
        else
            count <= count + 1;
    end
    
    always @ (posedge(clk))
    begin
         if (count == constantNumber - 1)
            clk_div <= ~clk_div;
        else
            clk_div <= clk_div;
    end
endmodule
