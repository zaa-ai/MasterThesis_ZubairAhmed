/**
 * Class: spi_master_register_seq
 * 
 * Read master register sequence.
 */
class spi_read_master_register_seq extends spi_master_register_seq;
	
	rand logic[11:0] burst_addresses[$];
	logic[15:0] burst_data[$];
	
	// indicates that this read command was incomplete (less words that needed)
	bit incomplete = 1'b0;
	// gets number of words in case of an incomplete read command
	int incomplete_word_count = 0;
	
	`uvm_object_utils_begin(spi_read_master_register_seq)
		`uvm_field_queue_int(burst_addresses, UVM_DEFAULT | UVM_HEX | UVM_NORECORD)
		`uvm_field_queue_int(burst_data, UVM_DEFAULT | UVM_HEX | UVM_NORECORD)
	`uvm_object_utils_end
	
	/************************ constraints ************************/
	
	covergroup cov_read_master_register with function sample(int burst_address_count);
		option.per_instance = 0;
		coverpoint burst_address_count {
			bins none = {0};
			bins few  = {1, 10};
			bins many = {11, 100};
			bins a_lot = default;
		}
	endgroup;
	
	/************************ Methods declarations ************************/
	function new(string name = "read master register");
		super.new(name);
		cov_read_master_register = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_read_master_register.sample(burst_addresses.size());
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_REG_READ;
	endfunction
		
	virtual function int get_word_count();
		if(incomplete == 1'b1) begin
			return incomplete_word_count;
		end
		return 2 + burst_addresses.size();
	endfunction	
	
	virtual function spi_mirroring_type get_mirroring_type();
		return spi_pkg::COMMAND_WORD_ONLY;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		if(index == 0) return super.get_word(index);
		if(index == burst_addresses.size() + 1) return {CMD_REG_READ, 12'h000};
		if(index > 0 && burst_addresses.size() > 0) return {CMD_REG_READ, burst_addresses[index - 1]};
		return super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		address = data_in[0][11:0];
		
		burst_addresses.delete();
		burst_data.delete();
				
		this.data_in.delete();
		this.data_out.delete();
		
		for (int i = 0; i < data_in.size(); i++) begin
			// take data
			if (i == 2) begin
				data = data_out[2];
			end
			if(i > 2) begin
				burst_data.push_back(data_out[i]);
			end
			if(data_in[i][15:12] != CMD_REG_READ) begin
				if(data_in[i-1] != {CMD_REG_READ, 12'h000}) begin
					incomplete = 1'b1;
					incomplete_word_count = i;
				end
				return 1'b1;
			end
			// this is needed to take care of two subsequent burst reads with 0x000 address
			if(i > 1 && data_in[i-1] == {CMD_REG_READ, 12'h000}) begin
				return 1'b1;
			end
			
			if(i > 0 && data_in[i][11:0] != 12'd0) begin
				burst_addresses.push_back(data_in[i][11:0]);
			end
			// copy in/out words
			this.data_in.push_back(data_in[i]);
			this.data_out.push_back(data_out[i]);
		end
		return 1'b0;
	endfunction
	
	virtual function string convert2string();
		return $sformatf("read 0x%04h (%s)",address, addresses_pkg::addresses[address]);
	endfunction
endclass


