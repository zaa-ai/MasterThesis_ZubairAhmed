/**
 * SPI seqence for SPI access of project 52307. 
 */
class buffer_write_seq extends buffer_writer_default_seq;
	
	rand logic[15:0]	data[$];
	rand bit			do_validation;
	rand bit			valid;
	logic[5:0]			ecc[$];
	
	`uvm_object_utils_begin(buffer_write_seq)
		`uvm_field_queue_int(data, UVM_DEFAULT | UVM_HEX)
		`uvm_field_int(valid, UVM_DEFAULT | UVM_BIN)
		`uvm_field_int(do_validation, UVM_DEFAULT | UVM_BIN)
	`uvm_object_utils_end
	`uvm_declare_p_sequencer(buffer_writer_sequencer_t)

	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("buffer_write_seq");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	task body();
		`uvm_info(get_type_name(), "buffer write sequence starting", UVM_HIGH)
		for (int word_index = 0; word_index < data.size(); word_index++) begin
			ecc.push_back(DWF_ecc_gen_chkbits(16, 6, data[word_index]));
			`uvm_do_on_with(req, p_sequencer, {action == BUFFER_WRITE; data == local::data[word_index]; ecc==local::ecc[word_index];})
		end
		if (do_validation == 1'b1) begin
			if (valid == 1'b1) begin
				`uvm_do_on_with(req, p_sequencer, {action == BUFFER_VALIDATE;})
			end
			else begin
				`uvm_do_on_with(req, p_sequencer, {action == BUFFER_INVALIDATE;})
			end
		end
		
		`uvm_info(get_type_name(), $sformatf("buffer write sequence completed: %s", this.convert2string()), UVM_HIGH)
	endtask : body
	
	function string convert2string();
		string s = super.convert2string();
		$sformat(s, {"%s\n" }, get_full_name(),);
		$sformat(s, {"data = %p\naccess = WRITE\n"}, data);
		$sformat(s, {"do_validation = %1b\t\t"}, do_validation);
		$sformat(s, {"valid = %1b"}, valid);
		return s;
	endfunction : convert2string
	
	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
	endfunction : do_record
	
endclass

class buffer_clear_seq extends buffer_writer_default_seq;
	
	`uvm_object_utils(buffer_clear_seq)
	`uvm_declare_p_sequencer(buffer_writer_sequencer_t)

	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("buffer_clear_seq");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	task body();
		`uvm_info(get_type_name(), "buffer clear sequence starting", UVM_HIGH)
		`uvm_do_on_with(req, p_sequencer, {action == BUFFER_CLEAR;})
		`uvm_info(get_type_name(), $sformatf("buffer clear sequence completed: %s", this.convert2string()), UVM_HIGH)
	endtask : body
	
	function string convert2string();
		string s = super.convert2string();
		$sformat(s, {"%s\n", "action = BUFFER_CLEAR\n" }, get_full_name());
		return s;
	endfunction : convert2string
	
	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
	endfunction : do_record
	
endclass
