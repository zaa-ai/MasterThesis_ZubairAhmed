class wgl_pattern_writer extends pattern_writer;
	
	virtual function void write_comment();
		// FIXME: implement something like that
		string current_comment = comments.pop_front();
		if (current_comment != "") begin
			current_comment = $sformatf(" {%s}",current_comment);
		end
	endfunction
endclass
