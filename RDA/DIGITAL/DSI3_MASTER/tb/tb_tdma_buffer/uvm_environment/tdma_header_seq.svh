/*------------------------------------------------------------------------------
 * File          : tdma_tr.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 26, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class tdma_header_seq extends tdma_seq;
	
	constraint co_target {target == HEADER;}
	
	`uvm_object_utils(tdma_header_seq)
	
	function new (string name = "tdma_header_sequence");
		super.new(name);
	endfunction
	
	static function tdma_header_seq	create_seq();
		tdma_header_seq	seq;
		seq = new();
		if (!seq.randomize())	begin 
			if (seq.uvm_report_enabled(UVM_NONE,UVM_ERROR,seq.get_type_name)) 
				seq.uvm_report_error (seq.get_type_name, "randomization of tdma_header_seq failed", UVM_NONE, `__FILE__, `__LINE__, "", 1); 
		end
		return seq;
	endfunction
	
endclass
