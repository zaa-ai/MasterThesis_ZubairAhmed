/**
 * Class: spi_command
 * 
 * Interface class that defines a SPI command.
 */
interface class spi_command;
	
	/**
	 * Gets 4 bit command code of this SPI command.
	 */
	pure virtual function spi_cmd_type get_command_code();
	
	/**
	 * Gets whether this SPI command start with given data word.
	 */
	pure virtual function bit starts_with(logic[15:0] word);
			
	/**
	 * Gets number of words.
	 */
	pure virtual function int get_word_count();
			
	/**
	 * Gets word at a given index.
	 */
	pure virtual function logic[15:0] get_word(int index);
	
	/**
	 * Gets word mirroring strategy for this command.
	 */
	pure virtual function spi_mirroring_type get_mirroring_type();
	
	/**
	 * Sets all properties of this spi_command to its values according given data_in and data_out vectors.
	 * 
	 * Returns:
	 *   returns '1' if all properties could be set successfully 
	 *   returns '0' if property setting failed (e.g. too few words contained in given data_in/data_out)
	 */
	pure virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
	
	/**
	 * Sample all coverage instances.
	 */
	pure virtual function void sample_cov();
	
endclass : spi_command;
