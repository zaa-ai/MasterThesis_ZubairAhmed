/**
 * Class: spi_read_status_seq
 * 
 * Sequence for reading IC status information via SPI
 */
class spi_read_status_seq extends spi_seq;
	
	spi_status_word	status;

	`uvm_object_utils_begin (spi_read_status_seq)
		`uvm_field_object(status, UVM_DEFAULT )
	`uvm_object_utils_end
	
	/************************ constraints ************************/
	
	/************************ Methods declarations ************************/
	function new(string name = "read IC status");
		super.new(name);
		status = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		status.sample_cov();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_STATUS_READ;
	endfunction
	
	virtual function spi_mirroring_type get_mirroring_type();
		return spi_pkg::NONE;
	endfunction
	
	virtual task body();
		super.body();
		if(is_first_of_frame) status.set(data_out[0]);
	endtask
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(is_first_of_frame) begin 
			status.set(data_out[0]);
		end
		else begin
			if(data_out.size() > 1) begin
				status.set(data_out[1]);
			end
		end
		return super.create_from(data_in, data_out);
	endfunction
	
	function void check_status_flags(spi_status_word_flags status_flags[$]);
		status.check_status_flags(status_flags);
	endfunction
	
endclass


