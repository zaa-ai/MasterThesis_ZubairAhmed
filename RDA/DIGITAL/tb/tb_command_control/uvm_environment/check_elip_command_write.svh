/**
 * Class: check_service
 *
 * Class for register write accesses from command buffer
 */
class check_elip_command_write  extends uvm_scoreboard;

	`uvm_component_utils(check_elip_command_write)

	uvm_analysis_imp_frame_writer	#(spi_command_frame_seq,	check_elip_command_write)  frame_export;
	uvm_analysis_imp_elip_writer	#(elip_tr, 					check_elip_command_write)  elip_export;

	protected data_ecc_t expected_elip_writes[$];
	protected data_ecc_t expected_elip_reads[$];

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
				data_ecc_t	command_data;
				shortint	ecc;
				command_data.data = t.commands[command_index].get_word(data_index);
				ecc = DWF_ecc_gen_chkbits(16,6, t.commands[command_index].get_word(data_index));
				command_data.ecc = ecc;
				expected_elip_writes.push_back(command_data);
				expected_elip_reads.push_back(command_data);
			end
		end
	endfunction

	`define expected_address_min 'h1000
	`define expected_address_max 'h1100

	function void write_elip_writer(elip_tr t);
		if (t.write == 1'b1) begin
			if (expected_elip_writes.size() > 0) begin
				data_ecc_t data = expected_elip_writes.pop_front();
				if (t.data_write != data.data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data written to ELIP! Expected %04h but got %04h", data.data, t.data_write))
				end
				if (t.data_write_ecc != data.ecc) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong ECC written to ELIP! Expected %04h but got %04h", data.ecc, t.data_write_ecc))
				end
				if ((t.address < 16'h1000) || (t.address >= 16'h1100)) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  `expected_address_min , `expected_address_max ))
				end
			end
			else begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("No access to buffer memory expected!"))
			end
		end
		else begin
			if (expected_elip_reads.size() > 0) begin
				data_ecc_t data = expected_elip_reads.pop_front();
				if (t.data_read != data.data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data read via ELIP! Expected %04h but got %04h", data.data, t.data_read))
				end
				if (t.data_read_ecc != data.ecc) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong ECC read via ELIP! Expected %04h but got %04h", data.ecc, t.data_read_ecc))
				end
				if ((t.address < 16'h1000) || (t.address >= 16'h1100)) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  `expected_address_min , `expected_address_max ))
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
