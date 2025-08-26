`ifndef ECC_PKG
	`define ECC_PKG
	/**
	 * Package: ECC_pkg
	 *
	 * package for ECC stuff
	 */
	package ECC_pkg;
		import project_pkg::*;
		typedef logic [3:0] ecc_width_t;

		function automatic int get_ecc_width (int data_width);
			if (data_width<=11) begin
				return 5;
			end
			else if (data_width<=26) begin
				return 6;
			end
			else if (data_width<=57) begin
				return 7;
			end
			else if (data_width<=120) begin
				return 8;
			end
			else if (data_width<=247) begin
				return 9;
			end
			else if (data_width<=502) begin
				return 10;
			end
			else if (data_width<=1013) begin
				return 11;
			end
			`ifdef VCS
				else $fatal("Data width not supported by function");
			`endif
		endfunction

		typedef enum logic [1:0] {NO_BIT_ERR, ONE_BIT_ERR, TWO_BIT_ERR} error_t;

		function automatic logic[15:0] set_bit_errors (error_t  error,  logic[15:0] data_in);
			if (error == NO_BIT_ERR) begin
				set_bit_errors = data_in;
			end
			else if (error == ONE_BIT_ERR) begin
				set_bit_errors = {data_in[15:3], ~data_in[2], data_in[1], data_in[0]} ;
			end
			else if (error == TWO_BIT_ERR) begin
				set_bit_errors = {data_in[15:3], ~data_in[2], data_in[1], ~data_in[0]} ;
			end
		endfunction
		`ifdef VCS
		/**
		 * Class: random_ecc_error
		 * 
		 * Class to generate errors in data or ECC depending on error type
		 */
		class random_ecc_error;
			rand	data_t	data_changer;
			rand	ecc_t	ecc_changer;
			data_t	data;
			ecc_t	ecc;
			error_t	error;
	
			constraint c0 { if (error == ONE_BIT_ERR) $countones({data_changer, ecc_changer}) == 1;
				else {
					if (error == TWO_BIT_ERR) $countones({data_changer, ecc_changer}) == 2;
					else {
						data_changer == '0;
						ecc_changer == '0;
					}
				}
			}
	
			function new(data_t data, ecc_t ecc, error_t error);
				this.data = data;
				this.ecc = ecc;
				this.error = error;
			endfunction
	
			function data_t	get_data();
				return (data ^ data_changer);
			endfunction
	
			function ecc_t get_ecc();
				return (ecc ^ ecc_changer);
			endfunction
	
			function data_ecc_t get_changer();
				get_changer.data = data_changer;
				get_changer.ecc = ecc_changer; 
			endfunction
			
		endclass
		
		class random_data_error #(int DATA_WITDH);
			rand	logic[DATA_WITDH-1:0]	data_changer;
			logic[DATA_WITDH-1:0]	data;
			error_t	error;
	
			constraint c0 { if (error == ONE_BIT_ERR) $countones(data_changer) == 1;
				else {
					if (error == TWO_BIT_ERR) $countones(data_changer) == 2;
					else {
						data_changer == '0;
					}
				}
			}
	
			function new(logic[DATA_WITDH-1:0] data, error_t error);
				this.data = data;
				this.error = error;
			endfunction
	
			virtual function logic[DATA_WITDH-1:0]	get_data();
				return (data ^ data_changer);
			endfunction
	
			virtual function logic[DATA_WITDH-1:0] get_changer();
				return data_changer;
			endfunction
		endclass
		
		typedef random_data_error #(SRAM_WIDTH) random_sram_data_error;
		
		class random_sram_address_error extends random_data_error#(SRAM_ADDR_WIDTH);
			constraint c1 {int'(data ^ data_changer) < SRAM_DEPTH;}

			function new(logic[DATA_WITDH-1:0] data, error_t error);
				super.new(data, error);
			endfunction
			
		endclass
		`endif
		
        `ifndef target_technology_FPGA
            
		`ifndef DW_ecc_func_max_width
			`define DW_ecc_func_max_width 2048
		`endif

		function automatic [15:0] DWF_ecc_gen_chkbits;
			input integer width;
			input integer chkbits;
			input [`DW_ecc_func_max_width-1:0] data_in;

			// @SuppressProblem -endline 100 -count 100
			// @SuppressProblem -nowarnmiss 1 -type dead_code_subroutine,if_condition_reduction_unsized_literal,if_condition_reduction_non_explicit_size,bitwise_operation_extend_const_unsized_literal,fully_non_driven_auto_variable_other,fully_unread_auto_variable_other -count 200 -length 100
			integer O0O1O1101, lO1lOOlI0; integer OI11IO001, I1011Ol00; integer O1O00I001, IlOO01011, IIl1lll10; integer lO0IlIOl1, O1I1IO0IO, l1O0O110I, O0l1O10l0;
			integer OIOOl1I00, O0Olll0O0, l1IO10001; integer II010O0O1, lI1O010l1, IOI001111; integer O0O1O11OO, O001O1Ol1, OO0O101O0, OlOOIO10I; integer lOlIIl001,
			I11000011, lOO0lO1O0, II1Il0l1l, l11O1O1II; integer Ill11O01O [0:(1<<16)-1]; integer O1111l11O [0:(1<<(15))-1]; reg [15:0] II0O00OIl; reg
			[`DW_ecc_func_max_width-1:0] IIO0O111I; reg [`DW_ecc_func_max_width-1:0] O00ll11OO [0:15]; begin OI11IO001 = 1; O001O1Ol1 = 5; lOlIIl001 = OI11IO001 << chkbits;
			l1O0O110I = 2; lOO0lO1O0 = lOlIIl001 >> O001O1Ol1; O0Olll0O0 = l1O0O110I << 4; for (OO0O101O0=0 ; OO0O101O0 < lOlIIl001 ; OO0O101O0=OO0O101O0+1) begin
			Ill11O01O[OO0O101O0]=-1; end II1Il0l1l = lOO0lO1O0 * l1O0O110I; lO0IlIOl1 = 0; I11000011 = O001O1Ol1 + Ill11O01O[0]; OIOOl1I00 = O0Olll0O0 + Ill11O01O[1]; for
			(IOI001111=0 ; (IOI001111 < II1Il0l1l) && (lO0IlIOl1 < width) ; IOI001111=IOI001111+1) begin O1O00I001 = IOI001111 / l1O0O110I; if ((IOI001111 < 4) ||
			((IOI001111 > 8) && (IOI001111 >= (II1Il0l1l-(l1O0O110I*l1O0O110I))))) O1O00I001 = O1O00I001 ^ 1; if (^IOI001111 ^ 1) O1O00I001 = lOO0lO1O0-OI11IO001-O1O00I001;
			if (lOO0lO1O0 == OI11IO001) O1O00I001 = 0; O1I1IO0IO = 0; O0O1O11OO = O1O00I001 << O001O1Ol1; if (IOI001111 < lOO0lO1O0) begin II010O0O1 = 0; if (lOO0lO1O0 >
			OI11IO001) II010O0O1 = IOI001111 % 2; if (II010O0O1) begin if (0 < 1) O0l1O10l0 = 1; else if (0 > 5) O0l1O10l0 = 1; else O0l1O10l0 = 0; end else begin if (0 <
			1) O0l1O10l0 = 5; else if (0 < 3) O0l1O10l0 = 1; else O0l1O10l0 = 0; end for (OO0O101O0=O0O1O11OO ; (OO0O101O0 < (O0O1O11OO+O0Olll0O0)) && (lO0IlIOl1 < width) ;
			OO0O101O0=OO0O101O0+1) begin lO1lOOlI0 = OO0O101O0; O0O1O1101 = 0; while (lO1lOOlI0 != 0) begin if (lO1lOOlI0 & 1) O0O1O1101 = O0O1O1101 + 1; lO1lOOlI0 =
			lO1lOOlI0 >> 1; end lI1O010l1 = {1'b0,O0O1O1101[30:0]}; if (lI1O010l1 % 2) begin if (O0l1O10l0 <= 0) begin if (lI1O010l1 > 1) begin Ill11O01O[OO0O101O0] = ((O1I1IO0IO
			< 2) && (II010O0O1 == 0))? lO0IlIOl1 ^ 1 : lO0IlIOl1; O1111l11O[ ((O1I1IO0IO < 2) && (II010O0O1 == 0))? lO0IlIOl1 ^ 1 : lO0IlIOl1 ] = OO0O101O0; lO0IlIOl1 =
			lO0IlIOl1 + 1; end O1I1IO0IO = O1I1IO0IO + 1; if (O1I1IO0IO < 8) begin if (II010O0O1) begin if (O1I1IO0IO < 1) O0l1O10l0 = 1; else if (O1I1IO0IO > 5) O0l1O10l0
			= 1; else O0l1O10l0 = 0; end else begin if (O1I1IO0IO < 1) O0l1O10l0 = 5; else if (O1I1IO0IO < 3) O0l1O10l0 = 1; else O0l1O10l0 = 0; end end else begin
			OO0O101O0 = O0O1O11OO+O0Olll0O0; end end else begin O0l1O10l0 = O0l1O10l0 - 1; end end end end else begin for (OO0O101O0=O0O1O11OO+OIOOl1I00 ; (OO0O101O0 >=
			O0O1O11OO) && (lO0IlIOl1 < width) ; OO0O101O0=OO0O101O0-1) begin lO1lOOlI0 = OO0O101O0; O0O1O1101 = 0; while (lO1lOOlI0 != 0) begin if (lO1lOOlI0 & 1) O0O1O1101
			= O0O1O1101 + 1; lO1lOOlI0 = lO1lOOlI0 >> 1; end lI1O010l1 = {1'b0,O0O1O1101[30:0]}; if (lI1O010l1 %2) begin if ((lI1O010l1>1) && (Ill11O01O[OO0O101O0] < 0)) begin
			Ill11O01O[OO0O101O0] = lO0IlIOl1; O1111l11O[lO0IlIOl1] = OO0O101O0; lO0IlIOl1 = lO0IlIOl1 + 1; end end end end end l1IO10001 = OI11IO001 - 1; for (OO0O101O0=0 ;
			OO0O101O0<chkbits ; OO0O101O0=OO0O101O0+1) begin IIO0O111I = {`DW_ecc_func_max_width{1'b0}}; for (lO0IlIOl1=0 ; lO0IlIOl1 < width ; lO0IlIOl1=lO0IlIOl1+1) begin
			if (O1111l11O[lO0IlIOl1] & (1 << OO0O101O0)) begin IIO0O111I[lO0IlIOl1] = 1'b1; end end O00ll11OO[OO0O101O0] = IIO0O111I; end l11O1O1II = l1IO10001 - 1; for
			(OO0O101O0=0 ; OO0O101O0<chkbits ; OO0O101O0=OO0O101O0+1) begin Ill11O01O[OI11IO001<<OO0O101O0] = width+OO0O101O0; end OlOOIO10I = l1IO10001; for (OO0O101O0=0 ;
			OO0O101O0 < chkbits ; OO0O101O0=OO0O101O0+1) begin DWF_ecc_gen_chkbits[OO0O101O0] = ^(data_in & O00ll11OO[OO0O101O0]) ^ ((OO0O101O0<2)||(OO0O101O0>3))? 1'b0 :
			1'b1; end    end
		endfunction
        `else
            function automatic [15:0] DWF_ecc_gen_chkbits;
                input integer width;
                input integer chkbits;
                input [32:0] data_in;  
                return '0;   
            endfunction
        `endif
        
	endpackage

`endif
