class elip_bus_seq extends elip_bus_default_seq;

	`uvm_field_utils_begin(elip_bus_seq)
	`uvm_field_utils_end
	`uvm_declare_p_sequencer(elip_bus_sequencer_t)

	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("elip_bus_seq");
	endfunction : new

	/************************ User defined methods declarations ************************/
	task body();
		`uvm_info(get_type_name(), "elip sequence starting", UVM_HIGH)
		`uvm_send (req)
		`uvm_info(get_type_name(), $sformatf("elip sequence completed: %s", this.convert2string()), UVM_HIGH)
	endtask : body

	function string convert2string();
		string s = super.convert2string();
		$sformat(s, {"%s\n", "address = %p\n" }, get_full_name(), req.address);
		if (req.write == 1'b1) begin
			$sformat(s, {"data_write = %p\naccess = WRITE\n"}, req.data_write);
			$sformat(s, {"data_ecc   = %p\naccess = WRITE\n"}, req.data_write_ecc);
		end
		else begin
			$sformat(s, {"data_read = %p\naccess = READ\n"}, req.data_read);
			$sformat(s, {"data_ecc  = %p\naccess = READ\n"}, req.data_read_ecc);
		end
		return s;
	endfunction : convert2string

	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
	endfunction : do_record

endclass : elip_bus_seq

class elip_read_seq extends elip_bus_default_seq;

	rand int address;
	int data;
	int ecc;

	`uvm_field_utils_begin(elip_read_seq)
	`uvm_field_int(address, UVM_DEFAULT | UVM_HEX)
	`uvm_field_int(data, UVM_DEFAULT | UVM_HEX)
	`uvm_field_int(ecc, UVM_DEFAULT | UVM_HEX)
	`uvm_field_utils_end
	`uvm_declare_p_sequencer(elip_bus_sequencer_t)

	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("elip_read_seq");
	endfunction : new

	/************************ User defined methods declarations ************************/
	task body();
		`uvm_info(get_type_name(), "elip read sequence starting", UVM_HIGH)
		`uvm_do_on_with(req, p_sequencer, {address == 16'(local::address); write == 1'b0;})
		data = req.data_read;
		ecc  = req.data_read_ecc;
		`uvm_info(get_type_name(), $sformatf("elip read sequence completed: %s", this.convert2string()), UVM_HIGH)
	endtask : body

	function string convert2string();
		string s = super.convert2string();
		$sformat(s, {"%s\t", "address = %p\t" }, get_full_name(), req.address);
		$sformat(s, {"data_read = %p\taccess = READ\n"}, data);
		$sformat(s, {"data_ecc  = %p\taccess = READ\n"}, ecc);
		return s;
	endfunction : convert2string

endclass

class elip_write_seq extends elip_bus_default_seq;

	rand int address;
	rand int data;
	rand int ecc;

	`uvm_field_utils_begin(elip_write_seq)
	`uvm_field_int(address, UVM_DEFAULT | UVM_HEX)
	`uvm_field_int(data, UVM_DEFAULT | UVM_HEX)
	`uvm_field_int(ecc, UVM_DEFAULT | UVM_HEX)
	`uvm_field_utils_end
	`uvm_declare_p_sequencer(elip_bus_sequencer_t)

	/************************ Methods declarations ************************/
	function new(string name ="");
		super.new("elip_write_seq");
	endfunction : new

	/************************ User defined methods declarations ************************/
	task body();
		`uvm_info(get_type_name(), "elip write sequence starting", UVM_HIGH)
		`uvm_do_on_with(req, p_sequencer, {address == 16'(local::address); write == 1'b1; data_write == 16'(local::data); data_write_ecc == 6'(local::ecc);})
		`uvm_info(get_type_name(), $sformatf("elip write sequence completed: %s", this.convert2string()), UVM_HIGH)
	endtask : body

	function string convert2string();
		string s = super.convert2string();
		$sformat(s, {"%s\t", "address = %p\t" }, get_full_name(), req.address);
		$sformat(s, {"data = %p\taccess = WRITE\n"}, data);
		$sformat(s, {"data = %p\taccess = WRITE\n"}, ecc);
		return s;
	endfunction : convert2string

endclass


