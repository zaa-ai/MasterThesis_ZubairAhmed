/*------------------------------------------------------------------------------
 * File          : tdma_tr.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 26, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class tdma_seq extends uvm_sequence #(tdma_tr, tdma_tr);
	
	rand	int				index;
	rand	bit				write;
	rand	tdma_target_t	target;
	
	rand	tdma_packet_t	packet_to_buffer;
	rand	tdma_header_t	header_to_buffer;
			tdma_packet_t	packet_from_buffer;
			tdma_header_t	header_from_buffer;
	
	`uvm_object_utils(tdma_seq)
	
	`uvm_declare_p_sequencer(tdma_sequencer)
	
	
	function new (string name = "tdma_header_sequence");
		super.new(name);
	endfunction
	
	virtual task body();
		
		`uvm_create_on(req, p_sequencer)
		set_data();
		`uvm_send(req)
		get_data();
		
	endtask
	
	virtual function void set_data();
		req.write = write;
		req.target = target;
		req.index = index;
		req.packet_to_buffer = packet_to_buffer;
		req.header_to_buffer = header_to_buffer;
	endfunction
	
	virtual function void get_data();
		packet_from_buffer = req.packet_from_buffer;
		header_from_buffer = req.header_from_buffer;
	endfunction
	
endclass
