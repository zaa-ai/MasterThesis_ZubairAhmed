/**
 * Class: spi_frame_factory_with_single_command
 * 
 * factory for creating SPI frame with only one command
 */
// @SuppressProblem -type class_not_in_hierarchy_tree -count 1 -length 1
class spi_frame_factory_with_single_command #(type T = spi_crm_seq) extends spi_command_frame_seq;
	
	`uvm_object_param_utils(spi_frame_factory_with_single_command #(T))

	function new(string name="spi_frame_factory_with_single_command");
		super.new(name);
	endfunction
	
	static function spi_command_frame_seq create_frame(spi_sequencer sequencer);
		spi_command_frame_seq new_frame = new();
		new_frame.set_sequencer(sequencer);
		new_frame.add_command(spi_seq_factory#(T)::create_seq());
		return new_frame;
	endfunction

endclass


