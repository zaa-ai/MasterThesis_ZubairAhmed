/*------------------------------------------------------------------------------
 * File          : tdma_tr.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Jan 26, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class tdma_tr extends uvm_sequence_item;
	rand	bit		write;
	rand	int		index;
	
	rand	tdma_target_t	target;
	
	rand	tdma_packet_t	packet_to_buffer;
	rand	tdma_header_t	header_to_buffer;
			tdma_packet_t	packet_from_buffer;
			tdma_header_t	header_from_buffer;
	
	`uvm_object_utils_begin(tdma_tr)
		`uvm_field_enum(tdma_target_t, target,UVM_DEFAULT)
	`uvm_object_utils_end
	
	function new(string name = "");
		super.new(name);
	endfunction
	
	function void do_print(uvm_printer printer);
		if (printer.knobs.sprint == 0)
			`uvm_info(get_type_name(), convert2string(), UVM_MEDIUM)
		else
			printer.m_string = convert2string();
	endfunction : do_print

	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
		`uvm_record_field("target", target)       
		`uvm_record_int("write", write, 1, UVM_BIN)
		case (target)
			HEADER: begin
				`uvm_record_int("in: earliest", packet_to_buffer.earliest, 16, UVM_DEC)
				`uvm_record_int("in: latest", packet_to_buffer.latest, 16, UVM_DEC)
				`uvm_record_int("in: info", packet_to_buffer.info, 16, UVM_DEC)
				`uvm_record_int("out:earliest", packet_from_buffer.earliest, 16, UVM_DEC)
				`uvm_record_int("out:latest", packet_from_buffer.latest, 16, UVM_DEC)
				`uvm_record_int("out:info", packet_from_buffer.info, 16, UVM_DEC)
			end
			PACKET: begin
				`uvm_record_int("    index", index, 16, UVM_DEC)
				`uvm_record_int("in: packet_count", header_to_buffer.packet_count, 16, UVM_DEC)
				`uvm_record_int("in: period", header_to_buffer.period, 16, UVM_DEC)
				`uvm_record_int("out:packet_count", header_from_buffer.packet_count, 16, UVM_DEC)
				`uvm_record_int("out:period", header_from_buffer.period, 16, UVM_DEC)
			end
		endcase
	endfunction : do_record

	function string convert2string();
		string s;
		$sformat(s, "%s\n", super.convert2string());
		$sformat(s, {"%s\n",
					"target     = %p\n", 
					"packet_to_buffer   = %p\n",           
					"header_to_buffer   = %p\n",
					"packet_from_buffer = %p\n",
					"header_from_buffer = %p\n"}, 
					get_full_name(), target, packet_to_buffer, header_to_buffer, packet_from_buffer, header_from_buffer);
		return s;
	endfunction : convert2string
	
endclass
