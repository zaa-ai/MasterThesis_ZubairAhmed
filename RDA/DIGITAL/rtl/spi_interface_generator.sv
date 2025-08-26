/**
 * Module: spi_interface_generator
 * 
 * module to generate spi_int_if from SPI pads
 */
module spi_interface_generator (
		spi_int_if.master 	spi_int,
		pad_int_if.master	csb,
		pad_int_if.master	sck,
		pad_int_if.master	sdi,
		pad_int_if.master	sdo,
		input	logic		i_scan_clock,
		input	logic		i_scan_reset,
		input	logic		i_scanmode,
		input	logic		i_sdi_scan_input,
		input	logic		i_csb_scan_input
	);
	
	logic	cs;
	assign	cs = (i_scanmode == 1'b0) ? ~csb.in_a : i_csb_scan_input;
	
	/*###   CSB   ######################################################*/
	assign	spi_int.csb = (i_scanmode == 1'b0) ? csb.in_a	: i_scan_clock;
	assign	csb.out		= 1'b0;
	assign	csb.oe	 	= 1'b0;
	assign	csb.ie	 	= 1'b1;
	assign	csb.pd	 	= 1'b0;
	assign	csb.pu 		= 1'b1;
	assign spi_int.csb_resn = (i_scanmode == 1'b0) ? cs : i_scan_reset;
	
	/*###   SCK   ######################################################*/
	// no scan functionality
	pure_clk_gate_latch i_pure_clk_gate_latch_sck (
			.in_clk_e    (cs        	), 
			.in_clk      (sck.in_a    	), 
			.out_clk     (spi_int.sck	), 
			.scan_mode   (i_scanmode    ));
	
	assign	sck.out		= 1'b0;
	assign	sck.oe		= 1'b0;
	assign	sck.ie		= 1'b1;
	assign	sck.pd 		= 1'b1;
	assign	sck.pu		= 1'b0;
	
	/*###   SDI   ######################################################*/
	assign	spi_int.sdi	= (i_scanmode == 1'b0) ? sdi.in_a   : i_sdi_scan_input;
	assign	sdi.out		= 1'b0;
	assign	sdi.oe		= 1'b0;			// scan data in 2
	assign	sdi.ie		= 1'b1;
	assign	sdi.pd		= 1'b1;
	assign	sdi.pu		= 1'b0;
	
	/*###   SDO   ######################################################*/
		//		sdo_pad.in_a	= (i_scanmode == 1'b0) ? I_SDO		 : 1'b0; //TODO: connect me
	assign	sdo.out		= spi_int.sdo;
	assign	sdo.oe		= ~csb.in_a;
	assign	sdo.ie		= 1'b0;			// scan data out 1
	assign	sdo.pd		= 1'b0;
	assign	sdo.pu		= 1'b0;

endmodule


