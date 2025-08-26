interface class spi_csb_handler;

	pure virtual function bit falling_csb_at_frame_start();
	
	pure virtual function bit csb_after_word(int word_index);
	
	pure virtual function bit rising_csb_at_frame_end();

endclass



class per_frame_csb_hander implements spi_csb_handler;
	
	virtual function bit rising_csb_at_frame_end();
		return 1'b1;
	endfunction
	
	virtual function bit falling_csb_at_frame_start();
		return 1'b1;
	endfunction
	
	virtual function bit csb_after_word(int word_index);
		return 1'b0;
	endfunction
	
	static function spi_csb_handler create();
		per_frame_csb_hander handler = new();
		return handler;
	endfunction
endclass


class per_word_csb_hander extends per_frame_csb_hander;
	
	virtual function bit csb_after_word(int word_index);
		return 1'b1;
	endfunction
	
	static function spi_csb_handler create();
		per_word_csb_hander handler = new();
		return handler;
	endfunction
endclass


class random_csb_hander implements spi_csb_handler;
	
	virtual function bit rising_csb_at_frame_end();
		return 1'($urandom_range(1,0));
	endfunction
	
	virtual function bit falling_csb_at_frame_start();
		return 1'b1;
	endfunction
	
	virtual function bit csb_after_word(int word_index);
		return 1'($urandom_range(1,0));
	endfunction
	
	static function spi_csb_handler create();
		random_csb_hander handler = new();
		return handler;
	endfunction
endclass

class always_high_csb_hander implements spi_csb_handler;
	
	virtual function bit rising_csb_at_frame_end();
		return 1'b0;
	endfunction
	
	virtual function bit falling_csb_at_frame_start();
		return 1'b0;
	endfunction
	
	virtual function bit csb_after_word(int word_index);
		return 1'b0;
	endfunction
	
	static function always_high_csb_hander create();
		always_high_csb_hander handler = new();
		return handler;
	endfunction
endclass

