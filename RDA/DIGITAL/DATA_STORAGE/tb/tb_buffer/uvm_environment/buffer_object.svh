/**
 * Class: buffer_object
 * 
 * TODO: Add class documentation
 */
class buffer_object extends uvm_report_object;
	
	protected	int	size;
	
	shortint unsigned written_data[$];
	shortint unsigned valid_data[$];
	
	function new(string name = "buffer");
		super.new(name);
		clear();
	endfunction
	
	virtual function void set_size(int size);
		this.size = size;
	endfunction
	
	virtual function void write(shortint unsigned data);
		written_data.push_back(data);
	endfunction
	
	virtual function void write_first(shortint unsigned data);
		written_data[0]=data;
	endfunction
	
	virtual function void validate();
		if (is_full()) begin
			invalidate();
		end
		else begin
			while(written_data.size() > 0) begin
				valid_data.push_back(written_data.pop_front());
			end
		end
	endfunction
	
	virtual function void invalidate();
		written_data.delete();
	endfunction
	
	virtual function void clear();
		written_data.delete();
		valid_data.delete();
	endfunction
	
	virtual function shortint unsigned read();
		return valid_data.pop_front();
	endfunction
	
	function bit is_full();
		if (written_data.size()+valid_data.size() > size) return 1'b1;
		else return 1'b0;
	endfunction
	
	function bit is_empty();
		if (valid_data.size() > 0) return 1'b0;
		else return 1'b1;
	endfunction
	
	virtual function void initialize();
		clear();
	endfunction
	
endclass


