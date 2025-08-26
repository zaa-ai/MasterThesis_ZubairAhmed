/*------------------------------------------------------------------------------
 * File          : tdma_tr.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 26, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class tdma_packet_seq extends tdma_seq;
	
	`uvm_object_utils(tdma_packet_seq)
	
	constraint co_target {target == PACKET;}
	constraint co_index {index > 0; index < 16;}
	
	function new (string name = "tdma_packet_sequence");
		super.new(name);
	endfunction
	
	static function tdma_packet_seq	create_seq();
		tdma_packet_seq	seq;
		seq = new();
		if (!seq.randomize())	begin 
			if (seq.uvm_report_enabled(UVM_NONE,UVM_ERROR,seq.get_type_name)) 
				seq.uvm_report_error (seq.get_type_name, "randomization of tdma_packet_seq failed", UVM_NONE, `__FILE__, `__LINE__, "", 1); 
		end
		return seq;
	endfunction
	
endclass
