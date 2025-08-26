/**
 * Simple subscriber for spi_read_pdcm_frame_seq that collects all reads in a simple queue.
 */
class spi_read_pdcm_subscriber extends uvm_subscriber #(spi_read_pdcm_frame_seq);
	
	`uvm_component_utils (spi_read_pdcm_subscriber)
	
	spi_read_pdcm_frame_seq reads[$] = '{};
	
	function new(string name = "read_crm_subscriber", uvm_component parent);
		super.new(name, parent);
	endfunction
	
	virtual function void write(spi_read_pdcm_frame_seq t);
		reads.push_back(t);
	endfunction
endclass