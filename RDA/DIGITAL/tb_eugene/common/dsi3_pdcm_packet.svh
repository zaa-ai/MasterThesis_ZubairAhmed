/**
 * Class: dsi3_pdcm_packet
 * 
 * PDCM message packet
 */
class dsi3_pdcm_packet extends dsi3_packet;
	
	rand dsi3_pkg::sid_length_e	source_id_symbols;
	
	`uvm_object_utils_begin(dsi3_pdcm_packet)
		`uvm_field_enum(dsi3_pkg::sid_length_e, source_id_symbols, UVM_DEFAULT)
	`uvm_object_utils_end
	
	constraint co_source_id_symbols_3 {(source_id_symbols >= 2 ) -> data.size() >= 4;}
	constraint co_order {solve data.size() before source_id_symbols;}
	constraint co_data { data.size() inside {[1:2048]};}
	
	function void post_randomize();
		update_crc();
	endfunction : post_randomize
	
	
	/************************ Methods declarations ************************/
	function new(string name = "dsi3_pdcm_packet");
		super.new(name);
	endfunction : new
	
	/************************ User defined methods declarations ************************/
	
	virtual function bit check_crc();
		crc_correct = crc_calculation_pkg::dsi3_calculate_correct_crc(data, source_id_symbols) === 16'h0000;
		return crc_correct;
	endfunction
	
	virtual function void update_crc();
		logic[15:0] calculated_crc;
		if(data.size() > 2) begin
			if(source_id_symbols == dsi3_pkg::SID_16Bit_CRC) begin
				if(data.size() > 4) begin
					repeat(4) void'(data.pop_back());
					calculated_crc = crc_calculation_pkg::dsi3_calculate_crc(crc_correct, data, source_id_symbols);
					repeat(4) data.push_back(4'd0);
					apply_crc_to_data(source_id_symbols, calculated_crc);
				end
			end
			else begin
				set_data_trailing_zeros(2);
				calculated_crc = crc_calculation_pkg::dsi3_calculate_crc(crc_correct, data, source_id_symbols);
				apply_crc_to_data(source_id_symbols, calculated_crc);
			end
		end
	endfunction
	
	local function void set_data_trailing_zeros(int count);
		for (int i = data.size() - 1; i >= data.size() - count; i--) begin
			data[i] = 4'h0;
		end
	endfunction
	
	local function void apply_crc_to_data(dsi3_pkg::sid_length_e sid, logic[15:0] calculated_crc);
		if(sid == dsi3_pkg::SID_16Bit_CRC) begin
			data[$-3] = calculated_crc[15:12];
			data[$-2] = calculated_crc[11:8];
		end
		data[$-1] = calculated_crc[7:4];
		data[$]   = calculated_crc[3:0];
	endfunction
	
	static function dsi3_pdcm_packet create_packet(logic[3:0] queue[$], dsi3_pkg::sid_length_e source_id_symbol_count);
		dsi3_pdcm_packet new_packet = new();
		new_packet.data = queue;
		new_packet.source_id_symbols = source_id_symbol_count;
		void'(new_packet.check_crc());
		return new_packet;
	endfunction
	
	/**
	 * Creates a new dsi3_pdcm_packet based on a queue of words.
	 */
	static function dsi3_pdcm_packet create_packet_16(logic[15:0] queue[$], dsi3_pkg::sid_length_e source_id_symbol_count, int symbol_count=-1);
		logic[3:0] l4_queue[$];
		void'(common_pkg::convert_queue #(16, 4)::convert(queue, l4_queue));
		if(symbol_count > 0) begin
			while(l4_queue.size() > symbol_count) begin
				void'(l4_queue.pop_back());
			end
		end
		return create_packet(l4_queue, source_id_symbol_count);
	endfunction
	
endclass 
