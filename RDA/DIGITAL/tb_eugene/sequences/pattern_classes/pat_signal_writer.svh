class pat_signal_writer implements signal_writer;
	
	virtual function string append_signal_value(string line, logic value, bit is_output);
		string new_line = line;
		if (new_line != "") new_line={new_line, " "};
		new_line = {new_line,make_string(value, ~is_output)};
		return new_line;
	endfunction
	
	virtual function string_stream append_signal_name(string_stream line, string signal);
		string_stream new_line = line;
		if (line.size() == 0) begin
			for (int index=0; index <signal.len(); index++) begin
				new_line.push_back(string'(signal[index]));
			end
		end
		else begin
			if (new_line.size()<signal.len()) begin : add_empty_lines
				string to_be_inserted = "";
				repeat (new_line[$].len())
					to_be_inserted = {to_be_inserted, " "};
				repeat (signal.len()-new_line.size()) begin
					new_line.push_back(to_be_inserted);
				end
			end
			for (int index=0; index < new_line.size(); index++) begin : add_empty_space
				new_line[index] = {new_line[index], " "};
			end
			for (int index=0; index < new_line.size(); index++) begin : add_signal_name
				int reverted_line_index = line.size() - index - 1;
				if (index < signal.len() )
					new_line[index] = {new_line[index], string'(signal[index])};
				else
					new_line[index] = {new_line[index], " "};
			end
		end
		return new_line;
	endfunction
	
	protected virtual function string make_string(logic value, logic select_input_for_IC=1'b0);
		if (select_input_for_IC) begin
			return $sformatf("%1b", value);
		end
		else begin
			case (value)
				1'b0: return $sformatf("L");
				1'b1: return $sformatf("H");
				1'bz: return $sformatf("Z");
				1'bx: return $sformatf("X");
			endcase
		end
	endfunction
	
endclass