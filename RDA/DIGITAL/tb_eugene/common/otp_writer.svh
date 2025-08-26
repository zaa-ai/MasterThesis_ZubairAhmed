  
/**
 * Definition of a generic OTP entry that can consist of multiple values (lines within OTP). 
 */ 
interface class otp_entry;
	
	/**
	 * Gets number of values (OTP lines) that are contained in this entry.
	 */
	pure virtual function int get_value_count();
	
	/**
	 * Gets value of given value index for a given OTP position.
	 */
	pure virtual function logic[11:0] get_value(int otp_position, int value_index);
	
endclass

/**
 * An empty OTP entry that adds zero values.
 */
class empty_otp_entry implements otp_entry;
	
	virtual function int get_value_count();
		return 1;
	endfunction
	
	virtual function logic[11:0] get_value(int otp_position, int value_index);
		return 12'h000;	
	endfunction
	
endclass

/**
 * Basic OTP entry that adds a single given value to OTP.
 */
class basic_otp_entry implements otp_entry;
	
	logic[11:0] value;
	
	function new(logic[11:0] otp_value);
		value = otp_value;
	endfunction
	
	virtual function int get_value_count();
		return 1;
	endfunction
	
	virtual function logic[11:0] get_value(int otp_position, int value_index);
		return value;	
	endfunction
	
endclass

/**
 * OTP entry that uses ECC protection, see https://confluence.elmos.de/x/6BLFAg
 */
class ecc_word_otp_entry extends uvm_object implements otp_entry;
	
	rand logic[15:0] value;
	logic[23:0] ecc_value;
	
	`uvm_object_utils_begin(ecc_word_otp_entry)
		`uvm_field_int (value, UVM_DEFAULT | UVM_NORECORD| UVM_HEX)
	`uvm_object_utils_end
	
	function new(string name = "");
		super.new("otp entry");
	endfunction
	
	virtual function int get_value_count();
		return 2;
	endfunction
	
	virtual function logic[11:0] get_value(int otp_position, int value_index);
		if(value_index == 0) begin
			ecc_value = calculate_ecc(otp_position, value);
			return ecc_value[23:12];
		end 
		return ecc_value[11:0];
	endfunction
	
	virtual function automatic logic[23:0] calculate_ecc(int position, logic[15:0] data);
		logic[27:0] bits; 
		int ecc_high = 0;
		int ecc_low  = 0;
		
		bits = {position[11:0], data};
		ecc_low  +=   1 * int'(     bits[ 1] ^ bits[ 2] ^ bits[ 3] ^ bits[ 5] ^ bits[ 8] ^ bits[ 9] ^ bits[11] ^ bits[14] ^ bits[17] ^ bits[18] ^ bits[19] ^ bits[21] ^ bits[24] ^ bits[25] ^ bits[27]); 
		ecc_low  +=   2 * int'(     bits[ 0] ^ bits[ 1] ^ bits[ 2] ^ bits[ 4] ^ bits[ 6] ^ bits[ 8] ^ bits[10] ^ bits[12] ^ bits[16] ^ bits[17] ^ bits[18] ^ bits[20] ^ bits[22] ^ bits[24] ^ bits[26]); 
		ecc_low  +=   4 * int'( 1 ^ bits[ 0] ^ bits[ 3] ^ bits[ 4] ^ bits[ 7] ^ bits[ 9] ^ bits[10] ^ bits[13] ^ bits[15] ^ bits[16] ^ bits[19] ^ bits[20] ^ bits[23] ^ bits[25] ^ bits[26]); 
		ecc_low  +=   8 * int'( 1 ^ bits[ 0] ^ bits[ 1] ^ bits[ 5] ^ bits[ 6] ^ bits[ 7] ^ bits[11] ^ bits[12] ^ bits[13] ^ bits[16] ^ bits[17] ^ bits[21] ^ bits[22] ^ bits[23] ^ bits[27]); 
		ecc_high +=   1 * int'(     bits[ 2] ^ bits[ 3] ^ bits[ 4] ^ bits[ 5] ^ bits[ 6] ^ bits[ 7] ^ bits[14] ^ bits[15] ^ bits[18] ^ bits[19] ^ bits[20] ^ bits[21] ^ bits[22] ^ bits[23]); 
		ecc_high +=   2 * int'(     bits[ 8] ^ bits[ 9] ^ bits[10] ^ bits[11] ^ bits[12] ^ bits[13] ^ bits[14] ^ bits[15] ^ bits[24] ^ bits[25] ^ bits[26] ^ bits[27]); 
		ecc_high +=   4 * int'(     bits[ 0] ^ bits[ 1] ^ bits[ 2] ^ bits[ 3] ^ bits[ 4] ^ bits[ 5] ^ bits[ 6] ^ bits[ 7] ^ bits[24] ^ bits[25] ^ bits[26] ^ bits[27]); 
		ecc_high +=   8 * int'(     bits[ 0] ^ bits[ 1] ^ bits[ 2] ^ bits[ 3] ^ bits[ 4] ^ bits[ 5] ^ bits[ 6] ^ bits[ 7] ^ bits[24] ^ bits[25] ^ bits[26] ^ bits[27]);

		return {ecc_high[3:0], data[15:8], ecc_low[3:0], data[7:0]};
	endfunction
	
endclass

class address_data_otp_entry extends ecc_word_otp_entry;
			
	rand logic[15:0] data;
	rand logic[11:0] address;

	logic[23:0] ecc_data;
	logic[23:0] ecc_address;
	
	rand bit single_bit_address_ecc_failure;
	rand bit double_bit_address_ecc_failure;
	rand int first_address_failure_position;
	rand int second_address_failure_position;
	
	rand bit single_bit_data_ecc_failure;
	rand bit double_bit_data_ecc_failure;
	rand int first_data_failure_position;
	rand int second_data_failure_position;
	
	`uvm_field_utils_begin(address_data_otp_entry)
		`uvm_field_int (data,    UVM_DEFAULT | UVM_NORECORD| UVM_HEX)
		`uvm_field_int (address, UVM_DEFAULT | UVM_NORECORD| UVM_HEX)
		`uvm_field_int (single_bit_address_ecc_failure, UVM_DEFAULT)
		`uvm_field_int (double_bit_address_ecc_failure, UVM_DEFAULT)
		`uvm_field_int (single_bit_data_ecc_failure, UVM_DEFAULT)
		`uvm_field_int (double_bit_data_ecc_failure, UVM_DEFAULT)
	
		`uvm_field_int (first_address_failure_position, UVM_DEFAULT | UVM_NORECORD| UVM_DEC)
		`uvm_field_int (second_address_failure_position, UVM_DEFAULT | UVM_NORECORD| UVM_DEC)
		`uvm_field_int (first_data_failure_position, UVM_DEFAULT | UVM_NORECORD| UVM_DEC)
		`uvm_field_int (second_data_failure_position, UVM_DEFAULT | UVM_NORECORD| UVM_DEC)
	`uvm_field_utils_end
		
	constraint co_single_bit_address_ecc_failure {(single_bit_address_ecc_failure == 1'b1) -> double_bit_address_ecc_failure == 1'b0;}
	constraint co_double_bit_address_ecc_failure {(double_bit_address_ecc_failure == 1'b1) -> single_bit_address_ecc_failure == 1'b0;}

	constraint co_single_bit_data_ecc_failure {(single_bit_data_ecc_failure == 1'b1) -> double_bit_data_ecc_failure == 1'b0;}
	constraint co_double_bit_data_ecc_failure {(double_bit_data_ecc_failure == 1'b1) -> single_bit_data_ecc_failure == 1'b0;}
	
	constraint co_first_address_failure_position { first_address_failure_position inside {[0:23]};}
	constraint co_second_address_failure_position { second_address_failure_position inside {[0:23]};}
	constraint co_address_failure_position { first_address_failure_position != second_address_failure_position;}
	
	constraint co_first_data_failure_position { first_data_failure_position inside {[0:23]};}
	constraint co_second_data_failure_position { second_data_failure_position inside {[0:23]};}
	constraint co_data_failure_position { first_data_failure_position != second_data_failure_position;}

	function new(string name= "");
		super.new("address data entry");
	endfunction 
	
	virtual function int get_value_count();
		return 4;
	endfunction
	
	virtual function logic[11:0] get_value(int otp_position, int value_index);
		if(value_index == 0) begin
			ecc_address = calculate_ecc(otp_position, {4'b0000,address});
			if(double_bit_address_ecc_failure == 1'b1 || single_bit_address_ecc_failure == 1'b1) ecc_address[first_address_failure_position] = ~ecc_address[first_address_failure_position];
			if(double_bit_address_ecc_failure == 1'b1) ecc_address[second_address_failure_position] = ~ecc_address[second_address_failure_position];
			return ecc_address[23:12];
		end 
		else if(value_index == 1) begin
			return ecc_address[11:0];
		end
		else if(value_index == 2) begin
			ecc_data = calculate_ecc(otp_position, data);
			if(double_bit_data_ecc_failure == 1'b1 || single_bit_data_ecc_failure == 1'b1) ecc_data[first_data_failure_position] = ~ecc_data[first_data_failure_position];
			if(double_bit_data_ecc_failure == 1'b1) ecc_data[second_data_failure_position] = ~ecc_data[second_data_failure_position];
			return ecc_data[23:12];
		end 
		else if(value_index == 3) begin
			return ecc_data[11:0];
		end
	endfunction
	
	virtual function bit is_ecc_error();
		return double_bit_address_ecc_failure == 1'b1 || double_bit_data_ecc_failure == 1'b1;
	endfunction
	
	
endclass

/**
 * This OTP writer class writes OTP files. 
 */
class otp_writer extends uvm_object;
	
	`uvm_object_utils(otp_writer)
		
	localparam int SIZE  			= 4096;
	
	empty_otp_entry empty = new();
	otp_entry entries[$];
	
	function new(string name = "");
		super.new("otp_writer");
	endfunction
		
	virtual function void add_entry(otp_entry entry);
		entries.push_back(entry);
	endfunction
	
	virtual function automatic void write(string file_name);
		int file = $fopen(file_name, "w");
		int position = 0;
		
		while (position < SIZE) begin
			otp_entry next_entry;
			if(entries.size() > 0) begin
				next_entry = entries.pop_front();
			end
			else begin
				next_entry = empty;
			end
			
			for (int value_index = 0; value_index < next_entry.get_value_count(); value_index++) begin
				if(position < SIZE) begin
					$fwrite(file, "%3h\n", next_entry.get_value(position, value_index));
					position++;
				end
			end
		end
		
		$fclose(file);
		`uvm_info(this.get_type_name(), $sformatf("wrote OTP file %s", file_name), UVM_MEDIUM)
	endfunction
	
endclass


class ecc_otp_writer extends otp_writer;
	
	/**
	 * Adds address/value pair ECC protected to OTP. 
	 */
	virtual function automatic void add_address_data(logic[15:0] address, logic[15:0] data);
		ecc_word_otp_entry address_entry = new();
		ecc_word_otp_entry data_entry = new();
		if(!address_entry.randomize() with {value == address;}) `uvm_error(this.get_name(), "randomization error")
		if(!data_entry.randomize() with {value == data;}) `uvm_error(this.get_name(), "randomization error")
		entries.push_back(address_entry);
		entries.push_back(data_entry);
	endfunction
	
endclass


