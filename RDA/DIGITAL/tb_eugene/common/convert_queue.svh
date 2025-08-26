/**
 * Class: convert_queue
 * 
 * Class for converting a queue of type logic with a certain width to another queue of type logic with a certain width 
 */
class convert_queue# (parameter size_in = 16, parameter size_out = 8);
			
	protected static bit bitstream[$];
			
	function new ();
				
	endfunction : new
			
	/*
	 * Function: convert
	 * Converts a queue of size 'size_in' to a queue of size 'size_out'.
	 * 
	 * Return
	 * 
	 * bit - bit is set to 0 if the input data queue cannot be converted without padding of x's 
	 * 
	 * */
	static function bit convert(logic[size_in-1:0] data_in[$], ref logic[size_out-1:0] data_out[$], input bit fill_with_zeros = 1'b0);
		data_out.delete();
		create_bitstream(data_in);
		return create_queue(data_out, fill_with_zeros);
	endfunction : convert
			
	protected static function void create_bitstream(logic[size_in-1:0] data[$]);
		bitstream.delete();
		for (int i=0; i<data.size(); i++) begin
			for (int k=$bits(data[i])-1; k>=0; k--) begin
				bitstream.push_back(data[i][k]);
			end
		end
	endfunction : create_bitstream
			
	protected static function bit create_queue(ref logic[size_out-1:0] data[$], input bit fill_with_zeros = 1'b0);
		bit size_warning=1'b0;
		while (bitstream.size() != 0) begin
			logic [size_out-1:0]	temp = 'x;
			for (int k=size_out-1; k>=0; k--) begin
				if (bitstream.size() != 0) begin
					temp[k] = bitstream.pop_front();
				end else begin
					if(fill_with_zeros) begin
						temp[k] = '0;
					end else begin
						size_warning = 1'b1;
					end
				end
			end
			data.push_back(temp);
		end
		return size_warning;
	endfunction : create_queue
			
endclass : convert_queue


