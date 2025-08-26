//                            -*- Mode: Verilog -*- 
//  Title           :
//  Project         :
//  (c) DMOS Design GmbH Dresden
//  This file may not be copied, modified, licensed, or distributed without 
//  express permission of DMOS Design GmbH Dresden. 
//  Unless an express warranty or other contract has been agreed there is 
//  no warranty provided, including merchantability and fitness for a 
//  particular purpose.
//  -----------------------------------------------------------------------------
//  CVS info        : $Id: header.el,v 1.1 2004/10/21 06:41:16 tle Exp $
//  Author          : Thomas Leitner -DMOS-
//  Created On      : Fri Nov 23 11:49:37 2007
//  -----------------------------------------------------------------------------
//  Status          : Unknown, Use with caution!
//  -----------------------------------------------------------------------------
//  HISTORY
//  
//  -----------------------------------------------------------------------------
//  PURPOSE
//  	|>Description of modules purpose<|
//  
//  -----------------------------------------------------------------------------
//  TABLE OF CONTENTS
//  
//  -----------------------------------------------------------------------------

//  -----------------------------------------------------------------------------
//  Modification of ROM_NIBBLE cells for CV018 technology
//  -----------------------------------------------------------------------------
//  17.02.2022   ile    ouput changed to vector
//  22.04.2022   ile    typo in _8 fixed
//                      model simplified
//  -----------------------------------------------------------------------------

`resetall
`timescale 1ns/10ps

module ROMNIBBLE_0( O );
   output [3:0] O;

   assign O =  4'h0;

endmodule

module ROMNIBBLE_1( O );
   output [3:0] O;

   assign O = 4'h1;

endmodule

module ROMNIBBLE_2( O );
   output [3:0] O;

   assign O = 4'h2;

endmodule

module ROMNIBBLE_3( O );
   output [3:0] O;

   assign O = 4'h3;

endmodule

module ROMNIBBLE_4( O );
   output [3:0] O;

   assign O = 4'h4;

endmodule

module ROMNIBBLE_5( O );
   output [3:0] O;

   assign O = 4'h5;

endmodule

module ROMNIBBLE_6( O );
   output [3:0] O;

   assign O = 4'h6;

endmodule

module ROMNIBBLE_7( O );
   output [3:0] O;

   assign O = 4'h7;

endmodule

module ROMNIBBLE_8( O );
   output [3:0] O;

   assign O = 4'h8;

endmodule

module ROMNIBBLE_9( O );
   output [3:0] O;

   assign O = 4'h9;

endmodule

module ROMNIBBLE_A( O );
   output [3:0] O;

   assign O = 4'hA;

endmodule

module ROMNIBBLE_B( O );
   output [3:0] O;

   assign O = 4'hB;

endmodule

module ROMNIBBLE_C( O );
   output [3:0] O;

   assign O = 4'hC;

endmodule

module ROMNIBBLE_D( O );
   output [3:0] O;

   assign O = 4'hD;

endmodule

module ROMNIBBLE_E( O );
   output [3:0] O;

   assign O = 4'hE;

endmodule

module ROMNIBBLE_F( O );
   output [3:0] O;

   assign O = 4'hF;

endmodule
