/**
 * Package: common_test_pkg
 * 
 * TODO: Add package documentation
 */
package common_test_pkg;
	typedef	logic[31:0] l32;
	typedef l32 l32_queue[$];
		
	typedef logic[15:0] l16;
	typedef l16 l16_queue[$];
		
	typedef logic[3:0] l4;
	typedef l4 l4_queue[$];
		
	function automatic l16 get_random_word();
		return $urandom;
	endfunction
		
	function automatic l16_queue create_random_values(int words);
		l16_queue temp;
		temp.delete();
		repeat(words)
			temp.push_back(get_random_word());
		return temp;
	endfunction		

endpackage


