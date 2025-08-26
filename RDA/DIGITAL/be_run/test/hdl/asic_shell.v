module asic_shell (
		input  TMODE,
		input  RESB__MDMA_DPIN, // scan_reset
		input  RFC__MDMA_DPIN, // scan enable
		input  MOSI__MDMA_DPIN, // scan data in 1
		output MISO__MDMA_DPIN, // scan data out 1
		input  DAB_TMS__MDMA_DPIN, // scan data in 2
		output INTB_TDO__MDMA_DPIN, //scan data out 2
		input  CSB__MDMA_DPIN, // scan data in 3
		inout  SYNCB_TDI__MDMA_DPIN, // scan data out3  // TDI
		input  BFWB_TCK__MDMA_DPIN, // scan clk / TCK
		input  SCK__MDMA_DPIN,
		input  PORB
		 );
	
  asic asic_inst(
  		.TMODE (TMODE),
  		.RESB  (RESB__MDMA_DPIN), // scan_reset
  		.RFC   (RFC__MDMA_DPIN), // scan enable
  		.SDI   (MOSI__MDMA_DPIN), // scan data in 1
  		.SDO   (MISO__MDMA_DPIN), // scan data out 1
  		.DAB   (DAB_TMS__MDMA_DPIN), // scan data in 2
  		.INTB  (INTB_TDO__MDMA_DPIN), //scan data out 2
  		.CSB   (CSB__MDMA_DPIN), // scan data in 3
  		.SYNCB (SYNCB_TDI__MDMA_DPIN), // scan data out3
  		.BFWB (BFWB_TCK__MDMA_DPIN),
		.SCK  (SCK__MDMA_DPIN),
		.PORB (PORB)
		);

endmodule
