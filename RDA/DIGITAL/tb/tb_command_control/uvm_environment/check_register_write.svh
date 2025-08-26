/**
 * Class: check_service
 * 
 * Class for register write accesses from command buffer
 */
class check_register_write  extends uvm_scoreboard;
	`uvm_component_utils(check_register_write)
	
	uvm_analysis_imp_frame_writer	#(spi_command_frame_seq,	check_register_write)  frame_export;
	uvm_analysis_imp_elip_writer	#(elip_tr, 			check_register_write)  elip_export;
	
	protected spi_seq expected_elip_writes[$];
	
	protected int	error_count;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		frame_export = new("frame_export", this);
		elip_export = new("elip_export", this);
	endfunction
	
	function void write_frame_writer(spi_command_frame_seq t);
		int command_index;
		for (command_index = 0; command_index<t.commands.size(); command_index++) begin
			if (t.commands[command_index].get_command_code() == CMD_REG_WRITE) begin
				spi_write_master_register_seq write;
				if ($cast(write, t.commands[command_index])) begin
					if ((write.address >= 'h20) && (write.address < 'h400))
						expected_elip_writes.push_back(t.commands[command_index]);
				end
			end
		end
	endfunction
	
	function void write_elip_writer(elip_tr t);
		if (expected_elip_writes.size() > 0) begin
			spi_seq seq = expected_elip_writes.pop_front();
			if (t.data_write != seq.data_in[1]) begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("Wrong data written to ELIP! Expected %04h but got %04h", seq.data_in[1], t.data_write))
			end
			if (t.address != {4'h0, seq.data_in[0][11:0]}) begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("Wrong address applied to ELIP! Expected %04h but got %04h", seq.data_in[1], t.data_write))
			end
		end
		else begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("No access to registers expected!"))
		end
	endfunction
	
	protected function void check_data();
		if (expected_elip_writes.size()>0) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Not all register writes done on ELIP! %0d remaining", expected_elip_writes.size()))
		end
	endfunction
	
	function void initialize();
		expected_elip_writes.delete();
		error_count = 0;
	endfunction
	
	function int get_error_count();
		check_data();
		return error_count;
	endfunction
	
endclass
