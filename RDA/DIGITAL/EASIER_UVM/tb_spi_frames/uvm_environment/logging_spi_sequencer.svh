
/**
 * spi sequencer implementation that just logs all incoming SPI transactions without sending them to any driver.
 */
class logging_spi_sequencer extends spi_sequencer;

	spi_tr transactions[$];
	int data_index;
	logic[15:0] data_out[$];
	
	`uvm_component_utils(logging_spi_sequencer)

	function new(string name = "logging_seqr", uvm_component parent = null);
		super.new(name, parent);
		clear();
		m_config = new();
		m_config.csb_handler = per_frame_csb_hander::create();
	endfunction : new
	
	function void clear();
		transactions = '{};
		data_out = '{};
		data_index = 0;
	endfunction

	virtual function void send_request(uvm_sequence_base sequence_ptr, uvm_sequence_item t, bit rerandomize = 1'b0);
		spi_tr transaction;
		if($cast(transaction, t)) begin
			transactions.push_back(transaction);
			if(transaction.tr_type == spi_pkg::SPI_DATA && data_index < data_out.size()) begin
				transaction.data_out = data_out[data_index];
				data_index++;
			end
		end
	endfunction
	
	virtual task wait_for_item_done(uvm_sequence_base sequence_ptr,	int transaction_id);
		// nothing to di here
		#1ns; // just waste some time
	endtask
	
	virtual task wait_for_grant(uvm_sequence_base sequence_ptr, int item_priority = -1, bit lock_request = 1'b0);
		#1ns;		
	endtask

endclass : logging_spi_sequencer 


