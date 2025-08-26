/**
 * Package: common_pkg
 * 
 * Common functions
 */
package common_lib_pkg;

	//==========================================================================
	// calculates bitwidth of a given number
	// special case: number 0 returns 1 !
	//==========================================================================
	
	function automatic int unsigned num2width(int unsigned num);
		// 0, 1			 => 1
		// 2, 3			 => 2
		// 4, 5, 6, 7 => 3
		// 8, ..., 15 => 4
		// and so on ...
		int unsigned number;
		int unsigned result;
		begin
			result = 1;
			number = num >> 1;
			while (number>0) begin
				result = result + 1;
				number = number >> 1;
			end
			num2width = result;
		end
	endfunction

endpackage


