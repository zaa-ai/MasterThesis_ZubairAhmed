/**
 * Class: check_service
 * 
 * Class for register write accesses from command buffer
 */
class check_elip_command_read_write  extends uvm_scoreboard;
	`uvm_component_utils(check_elip_command_read_write)
	
	uvm_analysis_imp_frame_writer	#(spi_command_frame_seq,	check_elip_command_read_write)  frame_export;
	uvm_analysis_imp_elip_writer	#(elip_tr, 					check_elip_command_read_write)  elip_export;
	
	protected shortint expected_elip_writes[$];
	protected shortint expected_elip_reads[$];
	protected shortint write_addresses[$];
	
	protected int	error_count;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		frame_export = new("frame_export", this);
		elip_export = new("elip_export", this);
	endfunction
	
	function void write_frame_writer(spi_command_frame_seq t);
		int command_index, data_index;
		for (command_index = 0; command_index < t.commands.size(); command_index++) begin
			for (data_index = 0; data_index<t.commands[command_index].get_word_count(); data_index++) begin
				expected_elip_writes.push_back(t.commands[command_index].get_word(data_index));
				expected_elip_reads.push_back(t.commands[command_index].get_word(data_index));
			end
		end
	endfunction
	
	local shortint expected_address_min = BASE_ADDR_DSI_CMD_BUF[0];
	local shortint expected_address_max = BASE_ADDR_DSI_CMD_BUF[0] + SIZE_DSI_CMD_BUF - 1;
	
	function void write_elip_writer(elip_tr t);
		if (t.write == 1'b1) begin
			if (expected_elip_writes.size() > 0) begin
				shortint data = expected_elip_writes.pop_front();
				if (t.data_write != data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data written to ELIP! Expected %04h but got %04h", data, t.data_write))
				end
				if ((t.address < expected_address_min) || (t.address > expected_address_max)) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  expected_address_min , expected_address_max ))
				end
				write_addresses.push_back(t.address);
			end
			else begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("No access to buffer memory expected!"))
			end
		end
		else begin
			if (expected_elip_reads.size() > 0) begin
				shortint data = expected_elip_reads.pop_front();
				shortint address = write_addresses.pop_front();
				if (t.data_read != data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data read via ELIP! Expected %04h but got %04h", data, t.data_read))
				end
				if ((t.address < expected_address_min) || (t.address > expected_address_max)) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  expected_address_min , expected_address_max ))
				end
				if (t.address != address) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address for read not the same as for write! Got %04h but should be %04h ", t.address,  address))
				end
			end
			else begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("No access to buffer memory expected!"))
			end
		end
	endfunction
	
	protected function void check_data();
		if (expected_elip_writes.size()>0) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Not all command writes done on ELIP! %0d remaining", expected_elip_writes.size()))
		end
		if (expected_elip_reads.size()>0) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Not all command reads done on ELIP! %0d remaining", expected_elip_reads.size()))
		end
		if (write_addresses.size()>0) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Not all addresses written are also read on ELIP! %0d remaining", write_addresses.size()))
		end
	endfunction
	
	function void initialize();
		expected_elip_writes.delete();
		expected_elip_reads.delete();
		write_addresses.delete();
		error_count = 0;
	endfunction
	
	function int get_error_count();
		check_data();
		return error_count;
	endfunction
	
endclass
