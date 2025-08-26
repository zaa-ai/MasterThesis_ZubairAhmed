
`include "dsi3_master_transmission_checker.svh"

class spi_reg_frontdoor extends uvm_reg_frontdoor;
	
	`uvm_object_utils(spi_reg_frontdoor)
	
	function new (string name = "");
		super.new(name);
	endfunction
  
	task body;
		uvm_reg register;
		uvm_reg_addr_t address;
		
		$cast(register, rw_info.element);
		address = register.get_address() & 64'h0000_0000_0000_ffff;
		
		if(rw_info.kind == UVM_WRITE) begin
			write_register(address);
		end 
		else begin
			read_register(address);
		end

		rw_info.status = UVM_IS_OK;
	endtask         
	
	task write_register(uvm_reg_addr_t address);
		spi_write_master_register_seq write;
		spi_tx_crc_request_seq crc_seq;
		spi_command_frame_seq frame;
		logic[11:0] target_address = (address > $size(uvm_reg_addr_t)'('hFFF)) ? 12'd0 : 12'(address);
		
		
		`uvm_create_on(frame, sequencer)
		`uvm_create(write);
		if (!write.randomize() with {address == target_address; data == 16'(rw_info.value[0]);}) begin
			`uvm_error(this.get_type_name(), "randomization failed for SPI write sequence in spi_reg_frontdoor")
		end
		frame.add_command(write);
		
		`uvm_create(crc_seq);
		if (!crc_seq.randomize() with {mosi_crc_correct == 1'b1;}) begin
			`uvm_error(this.get_type_name(), "randomization failed for SPI TX CRC sequence in spi_reg_frontdoor")
		end
		frame.add_command(crc_seq);
		`uvm_send(frame);
		#1us;
	endtask

	task read_register(uvm_reg_addr_t address);
		spi_read_master_register_seq read_seq;
		spi_tx_crc_request_seq crc_seq;
		spi_command_frame_seq frame;
		
		`uvm_create_on(frame, sequencer)
		`uvm_create(read_seq);
		
		if(16'(address) <= 16'h0FFF) begin
			// simple read
			if (!read_seq.randomize() with {address == 12'(local::address); burst_addresses.size()==0;}) begin
				`uvm_error(this.get_type_name(), "randomization failed for SPI read sequence in spi_reg_frontdoor")
			end
		end 
		else begin
			// use burst read to access address > 0xFFF
			if (!read_seq.randomize() with {address == 12'd0; burst_addresses.size()==1; burst_addresses[0]== (12'(local::address) & 12'hFFF);}) begin
				`uvm_error(this.get_type_name(), "randomization failed for SPI read sequence in spi_reg_frontdoor")
			end
		end
		
		frame.add_command(read_seq);
		`uvm_create(crc_seq);
		if (!crc_seq.randomize() with {mosi_crc_correct == 1'b1;}) begin
			`uvm_error(this.get_type_name(), "randomization failed for SPI TX CRC sequence in spi_reg_frontdoor")
		end
		frame.add_command(crc_seq);
		`uvm_send(frame);	
		
		rw_info.value[0] = (16'(address) <= 16'h0FFF) ? 64'(read_seq.data) : 64'(read_seq.burst_data[0]);
	endtask
	
endclass : spi_reg_frontdoor

class jtag_reg_frontdoor extends uvm_reg_frontdoor;
	
	`uvm_object_utils(jtag_reg_frontdoor)
	
	function new (string name = "");
		super.new(name);
	endfunction
  
	task body;
		uvm_reg register;
		uvm_reg_addr_t address;
		
		$cast(register, rw_info.element);
		address = register.get_address() & 64'h0000_0000_0000_ffff;
		
		if(rw_info.kind == UVM_WRITE) begin
			write_register(address);
		end 
		else begin
			read_register(address);
		end

		rw_info.status = UVM_IS_OK;
	endtask         
	
	task write_register(uvm_reg_addr_t address);
		jtag_write_elip_seq	write_seq;
		
		`uvm_create_on(write_seq, sequencer)
		if (!write_seq.randomize() with {address == 32'(local::address); data == 32'(rw_info.value[0]);}) begin
			`uvm_error(this.get_type_name(), "randomization failed for JTAG write ELIP sequence in jtag_reg_frontdoor")
		end
		`uvm_send(write_seq);
		#1us;
	endtask

	task read_register(uvm_reg_addr_t address);
		jtag_read_elip_seq	read_seq;
		
		`uvm_create_on(read_seq, sequencer)
		
		// use burst read to access address > 0xFFF
		if (!read_seq.randomize() with {address == 32'(local::address); init==1'b0;}) begin
			`uvm_error(this.get_type_name(), "randomization failed for JTAG read ELIP sequence in jtag_reg_frontdoor")
		end
		
		`uvm_send(read_seq);	
		
		rw_info.value[0] = read_seq.read_value;
	endtask
	
endclass

class jtag_frontdoor extends uvm_reg_frontdoor;
	
	`uvm_object_utils(jtag_frontdoor)
	
	function new (string name = "");
		super.new(name);
	endfunction
	
  
	task body;
		uvm_reg register;
		uvm_reg_addr_t address;
		
		$cast(register, rw_info.element);
		address = register.get_address() & 64'h0000_0000_0000_ffff;
		
		jtag_access(address);

		rw_info.status = UVM_IS_OK;
	endtask         
	
	task jtag_access(uvm_reg_addr_t address);
		jtag_tr	_jtag_tr;
		
		`uvm_info(this.get_type_name(), $sformatf("JTAG_IR = %2h  JTAG_DR = %8h", address, rw_info.value[0]), UVM_HIGH)
		`uvm_create_on(_jtag_tr, sequencer)
		if(!_jtag_tr.randomize() with {
				ir_length == 8;
				dr_length == 16;
				ir_value == {24'b0, local::address[7:0]};
				dr_value == {202'b0,local::rw_info.value[0]};
				init_jtag == 1'b0;}) begin
			`uvm_error(this.get_type_name(), "randomization failed for JTAG transaction in jtag_frontdoor")
		end
		`uvm_send(_jtag_tr)
		#1us;
		if(rw_info.kind == UVM_READ) begin
			rw_info.value[0] = {48'b0, _jtag_tr.read_dr[15:0]};
		end 
	endtask

endclass
