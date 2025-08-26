typedef	enum shortint {
	// start of SPI "frame" (e.g. CSN to low)
	SPI_START=0, 
	// SPI data word transmission
	SPI_DATA=1, 
	// end of SPI "frame" (e.g. CSN to high)
	SPI_END=2 } spi_tr_type;
