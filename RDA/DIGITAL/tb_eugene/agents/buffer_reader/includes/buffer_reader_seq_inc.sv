/**
 * SPI seqence for SPI access of project 52307. 
 */
class buffer_read_seq extends buffer_reader_default_seq;
	
	rand logic[15:0]	data[$];
	
	`uvm_object_utils_begin(buffer_read_seq)
		`uvm_field_queue_int(data, UVM_DEFAULT | UVM_HEX)
	`uvm_object_utils_end
	`uvm_declare_p_sequencer(buffer_reader_sequencer_t)

	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("buffer_read_seq");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	task body();
		`uvm_info(get_type_name(), "buffer read sequence starting", UVM_HIGH)
		for (int word_index = 0; word_index < data.size(); word_index++) begin
			`uvm_do_on_with(req, p_sequencer, {action == BUFFER_READ;})
			data[word_index]= req.data;
		end
		`uvm_info(get_type_name(), $sformatf("buffer read sequence completed: %s", this.convert2string()), UVM_HIGH)
	endtask : body
	
	function string convert2string();
		string s = super.convert2string();
		$sformat(s, {"%s\n" }, get_full_name(),);
		$sformat(s, {"data = %p\naccess = WRITE\n"}, data);
		return s;
	endfunction : convert2string
	
	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
	endfunction : do_record
	
endclass

class buffer_step_seq extends buffer_reader_default_seq;
	
	rand	int	step;
	
	`uvm_object_utils(buffer_step_seq)
	`uvm_declare_p_sequencer(buffer_reader_sequencer_t)

	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("buffer_step_seq");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	task body();
		`uvm_info(get_type_name(), "buffer step sequence starting", UVM_HIGH)
		`uvm_do_on_with(req, p_sequencer, {action == BUFFER_MOVE_POINTER; data == 16'(local::step);})
		`uvm_info(get_type_name(), $sformatf("buffer step sequence completed: %s", this.convert2string()), UVM_HIGH)
	endtask : body
	
	function string convert2string();
		string s = super.convert2string();
		$sformat(s, {"%s\n", "action = BUFFER_MOVE_POINTER\n" }, get_full_name());
		return s;
	endfunction : convert2string
	
	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
	endfunction : do_record
	
endclass
