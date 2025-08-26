/**
 * Class: check_service
 * 
 * Class for checking SPI communication
 */
class check_service  extends uvm_scoreboard;
	`uvm_component_utils(check_service)
	
	uvm_analysis_imp_reader	#(buffer_reader_tr,	check_service)  reader_export;
	uvm_analysis_imp_writer	#(buffer_writer_tr,	check_service)  writer_export;
	uvm_analysis_imp_elip	#(elip_tr,			check_service)  buffer_elip_export;
	
	typedef struct packed unsigned {
		data_t	address;
		data_t	data;
	} elip_access_t;
	
	protected int buffer_size;
	protected int buffer_offset;
	
	protected elip_access_t	elip_accesses[$];
	
	protected int	error_count;
	
	buffer_object	buffer;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		reader_export = new("reader_export", this);
		writer_export = new("writer_export", this);
		buffer_elip_export = new("buffer_elip_export", this);
		buffer = new();
	endfunction
	
	function void write_elip(elip_tr t);
		if (t.write == 1'b1) begin
			elip_access_t elip;
			elip.address = t.address;
			elip.data = t.data_write;
			elip_accesses.push_back(elip);
		end
		else begin
			elip_access_t expected;
			expected = elip_accesses.pop_front();
			if (t.address != expected.address) begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("Address is not expected! Expected 0x%4h but got 0x%4h", expected.address, t.address));
			end
			if (t.data_read != expected.data) begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("data is not expected! Expected 0x%4h but got 0x%4h", expected.data, t.data_read));
			end
			if ((t.address < buffer_offset) || (t.address >= buffer_offset + buffer_size)) begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("Address is not in expected range! Expected 0x%4h..0x%4h but got 0x%4h", buffer_offset, buffer_offset + buffer_size - 1, t.address));
			end
		end
	endfunction
	
	function void write_writer(buffer_writer_tr t);
		case (t.action)
			BUFFER_CLEAR:		buffer.clear();
			BUFFER_VALIDATE:	buffer.validate();
			BUFFER_INVALIDATE:	buffer.invalidate();
			BUFFER_WRITE:		begin
				buffer.write(t.data);
//				if (buffer.is_full() != t.full) begin
//					`uvm_error(this.get_type_name(), $sformatf("full flag is not set while buffer is full! Got %1b but expected %1b", t.full, buffer.is_full))
//				end
			end
			BUFFER_WRITE_FIRST:	buffer.write_first(t.data);
		endcase
	endfunction
	
	function void write_reader(buffer_reader_tr t);
		case (t.action)
			BUFFER_READ: begin
				shortint unsigned expexcted_data = buffer.read();
				if (expexcted_data != t.data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Read wrong data of buffer! Got %04h but exp. %04h", t.data, expexcted_data))
				end
			end
			BUFFER_MOVE_POINTER: begin
				repeat (t.data)
					void'(buffer.read());
			end
		endcase
		
	endfunction
	
	protected function check_data();
		
	endfunction
	
	function void set_buffer_size(int size);
		this.buffer_size = size;
		this.buffer.set_size(size);
	endfunction
	
	function void set_buffer_offset(int bo);
		this.buffer_offset = bo;
	endfunction
	
	function void initialize();
		buffer.initialize();
		elip_accesses.delete();
		error_count = 0;
	endfunction
	
	function int get_error_count();
		check_data();
		return error_count;
	endfunction
	
endclass
