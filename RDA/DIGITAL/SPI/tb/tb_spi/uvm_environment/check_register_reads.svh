/**
 * Class: check_register_reads
 *
 * Class for register write accesses from command buffer
 */
class check_register_reads  extends uvm_scoreboard;
	`uvm_component_utils(check_register_reads)

	uvm_analysis_imp_frame	#(spi_command_frame_seq,	check_register_reads)  frame_export;
	uvm_analysis_imp_elip	#(elip_tr, 					check_register_reads)  elip_export;

	typedef struct {
		int address;
		data_ecc_t data_read;
	} elip_reads_t;

	protected		elip_reads_t elip_read_data[$];
	protected int	error_count;

	function new(string name, uvm_component parent);
		super.new(name, parent);
		frame_export = new("frame_export", this);
		elip_export = new("elip_export", this);
	endfunction

	function void write_frame(spi_command_frame_seq t);
		int command_index, read_index;
		for (command_index = 0; command_index < t.commands.size(); command_index++) begin
			if (t.commands[command_index].get_type_name() == "spi_read_master_register_seq") begin
				spi_read_master_register_seq	read_seq;
				if ($cast(read_seq, t.commands[command_index])) begin
					elip_reads_t expected_read;
					if (elip_read_data.size() > 0) begin
						if (elip_read_data.size() != read_seq.burst_addresses.size()+1) begin
							error_count++;
							`uvm_error(this.get_type_name(), $sformatf("Number of ELIP read accesses(%1d) is not equivalent to number of SPI read accesses(%1d)!", elip_read_data.size(), read_seq.burst_addresses.size()+1))
						end
						else begin
							read_index = 0;
							while (elip_read_data.size() > 0) begin
								expected_read = elip_read_data.pop_front();
								if (read_index == 0) begin
                                    if(read_seq.data_in.size() > 1)
                                        check_expected_data(expected_read, read_seq.address, read_seq.data);
								end
								else begin
									if ((read_seq.burst_addresses.size() >= read_index) && (read_seq.burst_data.size() >= read_index)) begin
										check_expected_data(expected_read, read_seq.burst_addresses[read_index-1], read_seq.burst_data[read_index-1]);
									end
									else begin
										error_count++;
										`uvm_error(this.get_type_name(),$sformatf("read_index(%1d) is larger than burst read addresses(%1d) or data(%1d)!", read_index, read_seq.burst_addresses.size(), read_seq.burst_data.size()));
									end
								end
								read_index++;
							end
						end
					end
					else begin
						error_count++;
						`uvm_error(this.get_type_name(), $sformatf("Less ELIP accesses then SPI read data accesses!"))
					end
				end
				else begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Casting to spi_read_master_register_seq failed!"))
				end

			end
		end
		elip_read_data.delete();
	endfunction

	protected function void check_expected_data(elip_reads_t expected, int address, int data);
		ecc_t ecc = ecc_t'(DWF_ecc_gen_chkbits(16,6,data));
		if(address != expected.address) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Wrong address read via ELIP! Expected %04h but got %04h", address, expected.address))
		end
		if(data != expected.data_read.data) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Wrong data read via ELIP! Expected %04h but got %04h", expected.data_read.data, data))
		end
		if (ecc != expected.data_read.ecc) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Wrong ECC read via ELIP! Expected %04h but got %04h", expected.data_read.ecc, ecc))
		end
	endfunction

	function void write_elip(elip_tr t);
		if (t.write == 1'b1) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("No write access to registers expected!"))
		end
		else begin
			elip_reads_t elip_read;
			elip_read.address = t.address;
			elip_read.data_read.data = t.data_read;
			elip_read.data_read.ecc = t.data_read_ecc;
			elip_read_data.push_back(elip_read);
		end
	endfunction

	protected function void check_data();
		if (elip_read_data.size()>0) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Not all ELIP reads corresponded to SPI frame! %0d remaining", elip_read_data.size()))
		end
	endfunction

	function void initialize();
		elip_read_data.delete();
		error_count = 0;
	endfunction

	function int get_error_count();
		check_data();
		return error_count;
	endfunction

endclass
