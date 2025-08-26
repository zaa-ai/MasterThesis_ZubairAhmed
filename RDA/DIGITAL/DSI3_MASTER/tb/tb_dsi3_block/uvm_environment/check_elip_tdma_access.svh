/**
 * Class: check_service
 * 
 * Class for register write accesses from command buffer
 */
class check_elip_tdma_access  extends uvm_scoreboard;
	`uvm_component_utils(check_elip_tdma_access)
	
	parameter	shortint	BASE_ADDR_TDMA = 16'h2000;
	
	uvm_analysis_imp_frame_writer	#(spi_command_frame_seq,	check_elip_tdma_access)  frame_export;
	uvm_analysis_imp_elip_writer	#(elip_tr, 					check_elip_tdma_access)  elip_export;
	//FIXME: add TDMA scheme uploaded!
	protected expected_elip_access_t expected_elip_writes[$];
	protected expected_elip_access_t expected_elip_reads[$];
	
	protected int	error_count;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		frame_export = new("frame_export", this);
		elip_export = new("elip_export", this);
	endfunction
	
	function void write_frame_writer(spi_command_frame_seq t);
		
		int command_index, data_index;
		for (command_index = 0; command_index < t.commands.size(); command_index++) begin
			if (t.commands[command_index].get_command_code() == CMD_UPLOAD_TDMA) begin
				spi_upload_tdma_packet_seq		tdma_packet_seq;
				spi_validate_tdma_scheme_seq	validate_tdma_seq;
				if ($cast(tdma_packet_seq, t.commands[command_index])) begin
					if (tdma_packet_seq.channel_bits[0] == 1'b1) begin
						for (data_index = 1; data_index<t.commands[command_index].get_word_count(); data_index++) begin
							expected_elip_access_t new_write;
							new_write.data = tdma_packet_seq.get_word(data_index);
							new_write.address = BASE_ADDR_TDMA + tdma_packet_seq.packet_index * 3 + data_index + 1;
							expected_elip_writes.push_back(new_write);
						end
					end
				end
				if ($cast(validate_tdma_seq, t.commands[command_index])) begin
					if (validate_tdma_seq.channel_bits[0] == 1'b1) begin
						expected_elip_access_t new_write;
						new_write.data = validate_tdma_seq.get_word(0);
						new_write.address = BASE_ADDR_TDMA;
						expected_elip_writes.push_back(new_write);
						new_write.data = validate_tdma_seq.get_word(1);
						new_write.address = BASE_ADDR_TDMA+1;
						expected_elip_writes.push_back(new_write);
						//FIXME: add validation of scheme!
					end
				end
			end
		end
	endfunction
	
	local shortint expected_address_min = BASE_ADDR_TDMA;
	local shortint expected_address_max = BASE_ADDR_TDMA + 16'h0040 - 2;
	
	function void write_elip_writer(elip_tr t);
		if (t.write == 1'b1) begin
			if (expected_elip_writes.size() > 0) begin
				expected_elip_access_t expected = expected_elip_writes.pop_front();
				if ((t.address < expected_address_min) || (t.address > expected_address_max)) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  expected_address_min , expected_address_max ))
				end
				if (t.address != expected.address) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong address for writing on ELIP! Expected %04h but got %04h", expected.address, t.data_write))
				end
				if (t.data_write != expected.data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data written to ELIP address %04h! Expected %04h but got %04h", t.address,expected.data, t.data_write))
				end
			end
			else begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("No access to buffer memory expected!"))
			end
		end
		//FIXME: add reading of TDMA data!
//		else begin
//			if (expected_elip_reads.size() > 0) begin
//				shortint data = expected_elip_reads.pop_front();
//				shortint address = write_addresses.pop_front();
//				if (t.data_read != data) begin
//					error_count++;
//					`uvm_error(this.get_type_name(), $sformatf("Wrong data read via ELIP! Expected %04h but got %04h", data, t.data_read))
//				end
//				if ((t.address < expected_address_min) || (t.address > expected_address_max)) begin
//					error_count++;
//					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  expected_address_min , expected_address_max ))
//				end
//				if (t.address != address) begin
//					error_count++;
//					`uvm_error(this.get_type_name(), $sformatf("Address for read not the same as for write! Got %04h but should be %04h ", t.address,  address))
//				end
//			end
//			else begin
//				error_count++;
//				`uvm_error(this.get_type_name(), $sformatf("No access to buffer memory expected!"))
//			end
//		end
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
	endfunction
	
	function void initialize();
		expected_elip_writes.delete();
		expected_elip_reads.delete();
		error_count = 0;
	endfunction
	
	function int get_error_count();
		check_data();
		return error_count;
	endfunction
	
endclass
