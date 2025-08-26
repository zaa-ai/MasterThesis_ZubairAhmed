STIL 1.0 {
    Design 2005;
}
Header {
    Title "Minimal STIL for design `digtop'";
    Date "Wed Jun 25 16:57:49 2014";
    Source "DFT Compiler H-2013.03-SP4";
}
MacroDefs {
    "test_setup" {
        W "_default_WFT_";
        C {
            "all_inputs" = \r5 N;
            "all_outputs" = X;
        }
        
        V { // initial
            "I_RFC" = 0;
            "I_RESB" = 1;
            "I_CSB" = 1;
            "I_SCK" = 0;
            "I_PORB" = 1;
            "I_BFWB" = 0;  // TCK
            "I_TMODE" = 0;
            "I_DAB" = 0;   // TMS
            "I_SYNCB" = 0; // TDI
            "I_SDI" = 0;
            "I_SDO" = 0;
        }
        V { // reset
            "I_PORB" = 0;
            "I_CSB" = 0;
        }
        V { // set Test mode
        	"I_PORB" = 1;
        	"I_CSB" = 1;
        	"I_TMODE" = 1;
        }
// TAP STATE RESET
        Loop 5 {
            V {
                "I_BFWB" = P;
                "I_DAB"  = 1;
            }
        }
    	// -> RUN_IDLE
        V { 
            "I_BFWB" = P;
	        "I_DAB" = 0;
            "I_SYNCB" = 0;
        }
// -> 8 Bit IR = 0xb0 LSB first
        
        // -> Select_DR
        V { 
            "I_BFWB" = P;
            "I_DAB" = 1;
	        "I_SYNCB" = 0;
        }
        
        // -> Select_IR
        V { 
            "I_BFWB" = P;
            "I_DAB" = 1;
	        "I_SYNCB" = 0;
        }
        
        // -> CAPTURE_IR
        V {// -> IR = 0xb0 LSB first
            "I_BFWB" = P;
            "I_DAB" = 0;
	        "I_SYNCB" = 0;
        }
        
        // -> SHIFT_IR
        V { 
            "I_BFWB" = P;
            "I_DAB" = 0;
	        "I_SYNCB" = 0;
        }
        
        Loop 4 { //IR[0:3]=0x0
		V { 
            		"I_BFWB" = P;
            		"I_DAB" = 0;
	    	      	"I_SYNCB" = 0;
		}
        }
        
        Loop 2 { //IR[4:5]=11
		V { 
            		"I_BFWB" = P;
            		"I_DAB" = 0;
	    		    "I_SYNCB" = 1;
		}
        }
        
        // -> SHIFT_IR IR[6]=0
        V { 
            "I_BFWB" = P;
            "I_DAB" = 0;
	        "I_SYNCB" = 0;
        }
        
        // -> EXIT1_IR IR[7]=1
        V { 
            "I_BFWB" = P;
            "I_DAB" = 1;
	        "I_SYNCB" = 1;
        }
        
        // -> UPDATE_IR
        V { 
            "I_BFWB" = P;
            "I_DAB" = 1;
	        "I_SYNCB" = 0;
        }
      
	Loop 2 {
        // -> RUN_IDLE
        	V { 
            	"I_BFWB" = P;
            	"I_DAB" = 0;
	    	   	"I_SYNCB" = 0;
		      }
        }

        // -> Select_DR
        V { 
            "I_BFWB" = P;
            "I_DAB" = 1;
            "I_SYNCB" = 0;
        }
        // -> CAPTURE_DR
        V {
            "I_BFWB" = P;
            "I_DAB" = 0;
            "I_SYNCB" = 0;
        }
        
        // -> SHIFT_DR
        V { 
            "I_BFWB" = P;
            "I_DAB" = 0;
            "I_SYNCB" = 0;
        }
         
        // -> SHIFT_DR DR[0]=1 SCAN
        V { "I_BFWB" = P; "I_DAB" = 0; "I_SYNCB" = 1; }
        
        // -> SHIFT_DR DR[1]=0 VDD_RDIV_DIS
        V { "I_BFWB" = P; "I_DAB" = 0; "I_SYNCB" = 1; }
        
        // -> SHIFT_DR DR[2]=1 COMPRESSION
        V { "I_BFWB" = P; "I_DAB" = 0; "I_SYNCB" = 0; }

        // -> SHIFT_DR DR[3]=0 VDD_ILOAD_DIS
        V { "I_BFWB" = P; "I_DAB" = 0; "I_SYNCB" = 1;}

        // -> SHIFT_DR DR[4]=1 VDD_DIS
        V { "I_BFWB" = P; "I_DAB" = 0; "I_SYNCB" = 1; }

        // -> SHIFT_DR DR[5]=1 DISABLE_OSC
        V { "I_BFWB" = P; "I_DAB" = 0; "I_SYNCB" = 1; }

    Loop 9 {
        // -> SHIFT_DR DR[14:6]=0
        V { "I_BFWB" = P; "I_DAB" = 0; "I_SYNCB" = 0; }
      }
         // -> EXIT_DR DR[15]=0 TMS=1
        V { "I_BFWB" = P; "I_DAB" = 1; "I_SYNCB" = 0; }
        
        // -> UPDATE_DR
        V { "I_BFWB" = P; "I_DAB" = 1; "I_SYNCB" = 0; }
   
    Loop 2 {
            // -> RUN_IDLE
            V { 
                "I_BFWB" = P;
                "I_DAB" = 0;
                "I_CSB" = 0;
                "I_SYNCB" = 0;              
            }
        }
        V { 
            "I_BFWB" = 0;
        }
    }
}
