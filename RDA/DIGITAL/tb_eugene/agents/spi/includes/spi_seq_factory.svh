/**
 * Class: spi_seq_factory
 * 
 * factory for SPI sequences
 */
class spi_seq_factory #(type T) extends spi_seq;

	function new(string name="spi_seq_factory");
		super.new(name);
	endfunction
	
	static function T create_seq();
		T new_sequence = new();
		if(new_sequence.randomize() != 1) `uvm_error_context("spi_seq_factory", "randomization failed", new_sequence);
		return new_sequence;
	endfunction
	
	static function bit cast(spi_seq s, ref T t);
		bit result;
		result = 1'($cast(t,s));
		if (result == 1'b0) begin
			`uvm_error_context("spi_seq_factory", $sformatf("casting from spi_seq to %s failed!", T::type_name), s);
		end
		return result;
	endfunction

endclass


