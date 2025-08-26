/**
 * Class: receive_service
 * 
 * TODO: Add class documentation
 */
class receive_service extends uvm_object;
	
	int unsigned	recbuf_counter, recfin_counter;
	int unsigned	symbol_count;
	bit 			symbol_count_overflow;
	
	l16_queue	received_data;
	channel_mode_t	mode;
	
	function new();
		initialize();
	endfunction
	
	function void initialize();
		recbuf_counter = 0;
		recfin_counter = 0;
		received_data.delete();
		symbol_count = 0;
		symbol_count_overflow = 1'b0;
	endfunction
	
	function void receive_data(logic[15:0] data);
		received_data.push_back(data);
		recbuf_counter++;
	endfunction
	
	function void finish(logic overflow, byte unsigned symbol_count);
		recfin_counter++;
		this.symbol_count = symbol_count;
		this.symbol_count_overflow = overflow;
	endfunction
	
	virtual function bit compare_response(dsi3_slave_seq slave_seq);
		l4_queue	received_symbols;
		bit result = 1'b1;
		dsi3_packet packet_received = new();
		default_comparer#(.number_of_messages(10)) comparer = new();
		`uvm_info(this.get_type_name(), $sformatf("recfin_counter=%1d, recbuf_counter=%1d, data=%p", recfin_counter, recbuf_counter, received_data), UVM_DEBUG)
		`uvm_info(this.get_type_name(), $sformatf("slave_seq: %s", slave_seq.convert2string()), UVM_DEBUG)
		if (slave_seq.packet.data.size() < 4) begin
			result &= compare_for_empty_packet(packet_received, comparer);
		end
		else begin
            void'(convert_queue #(16, 4)::convert(received_data, received_symbols));
			while (received_symbols.size() > symbol_count) begin
				l4 symbol;
				symbol = received_symbols.pop_back();
				if (symbol != 4'h0) begin
					result &= 1'b0;
					`uvm_error(this.get_type_name, $sformatf("Symbol (0x%1h) is not empty", symbol))
				end
			end
			result &= check_counter_values(symbol_count, symbol_count_overflow);
			packet_received.data = received_symbols;
			if (mode == MODE_CRM) begin
				while (slave_seq.packet.data.size() > 8)
					void'(slave_seq.packet.data.pop_back());
				while (packet_received.data.size() > 8)
					void'(packet_received.data.pop_back());
			end
            void'(packet_received.compare(slave_seq.packet, comparer));
		end
		if (comparer.result != 0) begin
			result &= 1'b0;
			`uvm_error(this.get_type_name, $sformatf("There are mismatches in the packets"))
		end
		
		result &= check_symbol_count(symbol_count);
		result &= check_symbol_count_overflow(slave_seq, symbol_count_overflow);
		return result;
	endfunction
	
	virtual function bit compare_for_empty_packet(dsi3_packet packet_received, uvm_comparer comparer);
		bit result = 1'b1;
		dsi3_packet empty_packet = get_empty_dsi3_packet();
		void'(packet_received.compare(empty_packet, comparer));
		result &= check_counter_values(0, 0);
		return result;
	endfunction
	
	virtual function dsi3_packet get_empty_dsi3_packet();
		dsi3_packet empty_packet = new();
		return	empty_packet;
	endfunction
	
	function bit check_counter_values(int symbol_count, bit overflow);
		bit result = 1'b1;
		int temp = symbol_count;
		int recbuf_counter_from_symbol_count = 0;
		while (temp > 0) begin
			recbuf_counter_from_symbol_count++;
			temp -= 4;
		end
		if (symbol_count >= 4) begin
			if (recfin_counter != 1) begin
				`uvm_error(this.get_type_name, $sformatf("RECFIN counter is not equal 1. value = %1d", recfin_counter))
				result &= 1'b0;
			end
		end
		if (recbuf_counter_from_symbol_count != recbuf_counter) begin
			`uvm_error(this.get_type_name, $sformatf("RECBUF counter is not correct. Got %1d, exp. %1d", recbuf_counter, recbuf_counter_from_symbol_count))
			result &= 1'b0;
		end
		return result;
	endfunction
	
	function bit check_symbol_count(int expected_symbol_count);
		bit result = 1'b1;
		if (expected_symbol_count < 4) begin
			expected_symbol_count = 0;
		end
		else begin
			if (expected_symbol_count > 255) begin
				expected_symbol_count = 255;
			end
		end
		if (symbol_count != expected_symbol_count) begin
			`uvm_error(this.get_type_name(), $sformatf("unexpected symbol count! Exp. %d but got %d", expected_symbol_count, symbol_count))
			result = 1'b0;
		end
		return result;
	endfunction
	
	function bit check_symbol_count_overflow(dsi3_slave_seq slave_seq, bit symbol_count_overflow) ;
		bit result = 1'b1;
		int symbol_count;
		symbol_count = slave_seq.packet.data.size();
		if (symbol_count > 255 ) begin
			if (symbol_count_overflow != 1'b1) begin
				`uvm_error(this.get_type_name(), $sformatf("symbol count overflow is not set correctly! Exp. %1b but got %1b", 1'b1, symbol_count_overflow))
			end
		end
		return result;
	endfunction
	
endclass

