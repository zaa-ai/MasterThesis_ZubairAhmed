/**
 * DSI3 slave sequence 
 */
class dsi3_slave_seq extends dsi3_slave_default_seq;
	
	dsi3_packet	packet;
	
	`uvm_object_utils_begin(dsi3_slave_seq)
		`uvm_field_object (packet,	UVM_DEFAULT | UVM_NORECORD)
		`uvm_field_object (req, UVM_DEFAULT | UVM_NORECORD)
	`uvm_object_utils_end
	`uvm_declare_p_sequencer(dsi3_slave_sequencer_t)
	
	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("dsi3_slave_seq");
		req = new();
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	virtual task body();
		req.data = packet.data;
		`uvm_send (req);
		`uvm_info(get_type_name(), $sformatf("DSI3 Slave response: %s", this.convert2string()), UVM_DEBUG)
	endtask : body
	
	static function dsi3_slave_seq create_seq(dsi3_slave_tr t);
		dsi3_slave_seq new_seq = new();
		new_seq.packet = new();
		new_seq.packet.data = t.data;
		new_seq.req.copy(t);
		return new_seq;
	endfunction
	
	virtual function dsi3_slave_tr create_transaction(dsi3_slave_sequencer_t sequencer);
		`uvm_create_on (req, sequencer)
		return req;
	endfunction
	
	function void pack(ref logic[3:0] data_in[$]);
		data_in = packet.data;
	endfunction : pack
	
	function void unpack_data(logic[3:0] data_queue[$]);
		// FIXME: do it right!!!
		logic[15:0] queue[$];
		common_pkg::convert_queue#(4,16)::convert(data_queue, queue);
		packet.set_data(queue);
	endfunction : unpack_data 	
	
	function time get_begin_time();
		return req.get_begin_time();
	endfunction : get_begin_time
	
	function time get_end_time();
		return req.get_end_time();
	endfunction : get_end_time

	function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n", "%s\n"},
			get_full_name(), packet.convert2string());
		return s;
	endfunction : convert2string

	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
		if (packet != null) begin
			`uvm_record_field("packet", packet.convert2string())
		end
		req.do_record(recorder);
	endfunction : do_record
	
endclass : dsi3_slave_seq

class dsi3_slave_tr_container_seq extends dsi3_slave_default_seq;
	`uvm_object_utils(dsi3_slave_tr_container_seq)
	
	function new(string name ="");
		super.new("dsi3_slave_tr_container_seq");
	endfunction : new	
	
	task body();
		`uvm_send(req)
	endtask
endclass
