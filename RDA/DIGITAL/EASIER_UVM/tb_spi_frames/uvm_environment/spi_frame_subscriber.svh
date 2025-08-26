
/**
 * Simple subscriber for spi_command_frames that collects all frames in a simple queue.
 */
class spi_frame_subscriber extends uvm_subscriber #(spi_command_frame_seq);
	
	`uvm_component_utils (spi_frame_subscriber)
	
	spi_command_frame_seq frames[$] = '{};
	
	function new(string name = "frame subscriber", uvm_component parent);
		super.new(name, parent);
	endfunction
	
	virtual function void write(spi_command_frame_seq t);
		frames.push_back(t);
	endfunction
	
endclass