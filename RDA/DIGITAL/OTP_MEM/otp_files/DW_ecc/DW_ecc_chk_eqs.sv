////////////////////////////////////////////////////////////////////////////////
//
//       This confidential and proprietary software may be used only
//     as authorized by a licensing agreement from Synopsys Inc.
//     In the event of publication, the following notice is applicable:
//
//                    (C) COPYRIGHT 2019 SYNOPSYS INC.
//                           ALL RIGHTS RESERVED
//
//       The entire notice above must be reproduced on all authorized
//     copies.
//
// AUTHOR:    Synopsys DesignWare Team, 7/18/2014
//
// VERSION:   Verilog Check-bit Calculation 
//
//
////////////////////////////////////////////////////////////////////////////////


`timescale 1ns / 1ns

module DW_ecc_chk_eqs();

	// In order to allow the Verilog simulator to find the following include
	// file in the DC directory tree, pleas add  +incdir+$SYNOPSYS/dw/sim_ver
	// to you Verilog simulator command line
	//
	// For example, for the Synopsys VCS simulator (assuming $SYNOPSYS points
	// to a DC directory tree and the user's search path includes the directory
	// where the vcs executable is located:
	//
	//   vcs -R +incdir+$SYNOPSYS/dw/sim_ver DW_ecc_chk_eqs.v
	//
	`include "DW_ecc_function.inc"


	// In order to generate the information for a specific configuration of DW_ecc
	// you can either:
	//
	// 1. Modify the default parameter values in this file before simulation
	//    Example for Synopsys' VCS simulator:
	//
	//     vcs -R +incdir+$SYNOPSYS/dw/sim_ver DW_ecc_chk_eqs.v
	//
	//  or
	//
	// 2. Use simulator command line options to override the default parameter values
	//    for simulation (without modifying this file).
	//    Example for Synopsys' VCS simulator:
	//
	//     vcs -R +incdir+$SYNOPSYS/dw/sim_ver -pvalue+width=68 \
	//         -pvalue+chkbits=8 DW_ecc_chk_eqs.v
	//
	parameter width = 64;
	parameter chkbits = 8;
	bit is_first;
	initial begin : chek_bit_gen

		integer i,j,k,x,y;

		integer eqn_file;
		reg [15 : 0]		chk_bits_rtn;
		reg [chkbits-1 : 0]         act_check_bits[width-1 : 0] ;
		reg [chkbits-1 : 0]         inv_chk;
		reg [chkbits-1 : 0]         tmp_chk;
		reg [width-1 : 0]           chk_bit_eqn [chkbits-1 :0];
    
		reg [width-1 : 0]           data_zero;
		reg [width-1 : 0]           tmp_data;

		// check parameter legality
		if ( width > ((1 << (chkbits-1))-chkbits) ) begin
			$display( " " );
			$display( "*** *** *** *** *** *** *** *** *** *** *** *** *** ***" );
			$display( "***  Error!  specified width (%0d) is too large to", width );
			$display( "***  be protected by the specified number of check bits" );
			$display( "***  (chkbits specified to be %0d)", chkbits );
			$display( "*** *** *** *** *** *** *** *** *** *** *** *** *** ***" );
			$display( " " );
			$finish;
		end

		if ( width <= (1 << (chkbits-2))-chkbits-1 ) begin
			$display( " " );
			$display( "*** *** *** *** *** *** *** *** *** *** *** *** *** ***" );
			$display( "***  Warning!  specified number of check bits (%0d) is", chkbits );
			$display( "***  more than is needed to protect the specified number" );
			$display( "***  of data bits (width specified to be %0d)", width );
			$display( "*** *** *** *** *** *** *** *** *** *** *** *** *** ***" );
			$display( " " );
		end

		// Open output file using file designator, eqn_file
		eqn_file = $fopen("DW_ecc_equations.txt");

		data_zero = {width{1'b0}};
		tmp_data  = {data_zero[width-1:1], 1'b1};

		$fdisplay(eqn_file,"-- *****************************************************  ");
		$fdisplay(eqn_file,"--  Configured for %0d data bits and %0d check bits", width, chkbits);
		$fdisplay(eqn_file,"-- *****************************************************  ");
  

		chk_bits_rtn = DWF_ecc_gen_chkbits(width, chkbits, data_zero);
		inv_chk = chk_bits_rtn[chkbits-1 : 0];

		for (i=0 ; i< width ; i=i+1) begin
      
			// generate 16bit check bit value for each data bit
			chk_bits_rtn = DWF_ecc_gen_chkbits(width, chkbits,tmp_data);
			act_check_bits[i] = chk_bits_rtn[chkbits-1 : 0] ^ inv_chk;
			tmp_data = tmp_data << 1;
		end

		for (i=0 ; i < chkbits ; i=i+1) begin
			tmp_chk = {chkbits{1'b0}};
			tmp_chk[i] = 1'b1;
		end

		for (j=0; j< width; j=j+1) begin
			for (k=0; k< chkbits ; k=k+1) begin
				chk_bit_eqn[k][j] = act_check_bits[j][k];
			end
		end
    
		$fdisplay(eqn_file,"-- ");
		$fdisplay(eqn_file,"-- ***************************************************** ");
		$fdisplay(eqn_file,"--  Generation of check bit equations  ");
		$fdisplay(eqn_file,"-- *****************************************************" );
		$fdisplay(eqn_file,"-- ");
   
 
		for (x=0; x< chkbits; x=x+1) begin
			string invert = "    ";
			is_first = 1'b1;
			
			if (inv_chk[x] == 1'b1) begin
				invert = "1 ^ ";
			end 
			$fwrite(eqn_file,$sformatf("$parity += %3d * ( %s", 1<<x, invert));
			for (y =0; y< width; y=y+1) begin
				if (chk_bit_eqn[x][y] == 1'b1) begin
					if (is_first == 1'b0)
						$fwrite (eqn_file," ^ ");
					$fwrite (eqn_file,"$bits[%2d]", y);
					is_first = 1'b0;
				end
			end  

			$fdisplay(eqn_file,"); ");
		end 
 
		$fdisplay(eqn_file," ");

		$display( " " );
		$display( "***" );
		$display( "*** Syndrome mappings and check bit equation information have  ***" );
		$display( "*** been written to the text file, DW_ecc_equations.txt        ***" );
		$display( "***" );
		$display( " " );

		$finish;

	end

endmodule
