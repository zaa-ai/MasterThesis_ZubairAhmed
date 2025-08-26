/**
 * Interface: spi_int_if
 * 
 * internal SPI interface
 */
interface spi_int_if;
	logic	csb, sck, sdi, sdo, csb_resn;
	
	modport master (
			input sdo, output sck, sdi, csb, csb_resn
		);
	
	modport slave (
			input sck, sdi, csb, csb_resn, output sdo
		);
	

endinterface


