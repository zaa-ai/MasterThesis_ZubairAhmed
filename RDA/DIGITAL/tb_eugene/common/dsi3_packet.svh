/*
 * Class: dsi3_packet
 *
 * DSI3 packet including CRC and data
 */
class dsi3_packet extends uvm_object;
	
	rand logic[3:0]		data[$];
	rand logic			crc_correct;
	
	constraint co_data				{ data.size() inside {[1:2048]};}
	constraint co_crc_correct_weight {crc_correct dist {0:=1, 1:=2};}
	
	`uvm_field_utils_begin(dsi3_packet)
		`uvm_field_queue_int (data, UVM_DEFAULT | UVM_NORECORD| UVM_HEX)
	`uvm_field_utils_end

	/************************ Methods declarations ************************/
	function new(string name = "dsi3_packet");
		super.new(name);
	endfunction : new
	
	/************************ User defined methods declarations ************************/
	/*	
	 * Function: get_data_in_words
	 * 
	 * Builds a queue of words from data
	 * 
	 * Parameters:
	 * - by reference logic[15:0] words[$] 
	 * 
	 * Returns:
	 *   void
	 */
	virtual function void get_data_in_words (ref logic[15:0] words[$]);
		void'(common_pkg::convert_queue#(4,16)::convert(data, words));
	endfunction
	
	/*	
	 * Function: set_data
	 * 
	 * Sets the internal data to values from the data input stream (queue)
	 * 
	 * Parameters:
	 * - logic[15:0] queue[$] - input data stream as queue 
	 * 
	 * Returns:
	 *   void
	 */
	virtual function void set_data(logic[15:0] queue[$]);
		void'(common_pkg::convert_queue#(16,4)::convert(queue, data));
	endfunction
	
	/*	
	 * Function: get_word
	 * 
	 * Returns the word of the object packed queue with index <index>
	 * 
	 * Parameters:
	 * - int index
	 * 
	 * Returns:
	 *   logic[15:0] - word
	 */
	virtual function logic[15:0] get_word (int index);
		logic[15:0]  que[$];
		this.get_data_in_words(que);
		if ((index < que.size()) && (index >=0)) 
			return que[index];
		else begin
			`uvm_error(this.get_type_name(), $sformatf("Index for request is not available: req=%1d, max=%1d", index, que.size()-1)); 
			return 0;
		end
	endfunction : get_word
	
	virtual function bit check_crc();
		`uvm_error(this.get_type_name(), "called check_crc function from dsi3_packet!")
		return 1'b0;
	endfunction
	
	/**
	 * Changes current symbol count of this packet (removes symbols from packet data) and recalculates CRC.
	 */
	virtual function void change_symbol_count(int new_symbol_count);
		while(data.size() > new_symbol_count) begin
			void'(data.pop_back());
		end
		void'(check_crc());
	endfunction
	
	virtual function int get_word_count();
		return data.size() / 4;
	endfunction
	
	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
		for (int i=0; i < get_word_count(); i++) begin
			`uvm_record_field($sformatf("word_%0d",i+1), $sformatf("0x%04h", get_word(i)))
		end
	endfunction : do_record
	
	function string convert2string();
		string s;
		s = $sformatf("%s, %s\ncrc_correct = %1b, data = [", super.convert2string(), get_full_name(), crc_correct);
		for (int i = 0; i < data.size; i++) begin
			s=$sformatf("%s%0h ", s, data[i]);
		end
		s = $sformatf("%s]",s);
		return s;
	endfunction : convert2string

endclass : dsi3_packet
