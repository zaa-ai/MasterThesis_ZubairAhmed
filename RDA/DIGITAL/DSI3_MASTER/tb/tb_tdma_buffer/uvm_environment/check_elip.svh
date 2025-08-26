/**
 * Class: check_service
 * 
 * Class for register write accesses from command buffer
 */
class check_elip  extends uvm_scoreboard;
	`uvm_component_utils(check_elip)
	
	uvm_analysis_imp_elip	#(elip_tr, 					check_elip)  elip_export;
	
	protected shortint expected_elip_writes[$];
	protected shortint expected_elip_reads[$];
	protected shortint write_addresses[$];
	protected shortint read_addresses[$];
	
	tdma_packet_t	packets[16];
	tdma_header_t	header;
	
	protected int	error_count;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		elip_export = new("elip_export", this);
		foreach (packets[i]) begin
			packets[i].earliest = '0;
			packets[i].latest = '0;
			packets[i].info = '0;
		end
	endfunction
	
	shortint base_address;
	shortint size;
	
	function void write_tdma(tdma_seq t);
		case (t.write)
			// read
			0: begin
				case (t.target)
					HEADER: begin
						expected_elip_reads.push_back(header.packet_count.data);
						expected_elip_reads.push_back(header.period.data);
						read_addresses.push_back(base_address);
						read_addresses.push_back(base_address+1);
					end
					PACKET: begin
						expected_elip_reads.push_back(packets[t.index].earliest.data);
						expected_elip_reads.push_back(packets[t.index].latest.data);
						expected_elip_reads.push_back(packets[t.index].info.data);
						read_addresses.push_back(base_address+2+(t.index *3)+0);
						read_addresses.push_back(base_address+2+(t.index *3)+1);
						read_addresses.push_back(base_address+2+(t.index *3)+2);
					end
				endcase
			end
			// write
			1: begin
				case (t.target)
					HEADER: begin
						expected_elip_writes.push_back(t.header_to_buffer.packet_count.data);
						expected_elip_writes.push_back(t.header_to_buffer.period.data);
						write_addresses.push_back(base_address);
						write_addresses.push_back(base_address+1);
						header = t.header_to_buffer;
					end
					PACKET: begin
						expected_elip_writes.push_back(t.packet_to_buffer.earliest.data);
						expected_elip_writes.push_back(t.packet_to_buffer.latest.data);
						expected_elip_writes.push_back(t.packet_to_buffer.info.data);
						write_addresses.push_back(base_address+2+(t.index *3)+0);
						write_addresses.push_back(base_address+2+(t.index *3)+1);
						write_addresses.push_back(base_address+2+(t.index *3)+2);
						packets[t.index] = t.packet_to_buffer;
					end
				endcase
			end
		endcase
	endfunction
	
	function void write_elip(elip_tr t);
		if (t.write == 1'b1) begin
			if (expected_elip_writes.size() > 0) begin
				shortint data = expected_elip_writes.pop_front();
				shortint address = write_addresses.pop_front();
				if (t.data_write != data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data written to ELIP! Expected %04h but got %04h", data, t.data_write))
				end
				if ((t.address < base_address) || (t.address > base_address + size)) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  base_address , base_address + size ))
				end
				if (t.address != address) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address is not correct! Got %04h but expected %04h ", t.address,  address))
				end
			end
			else begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("No write access to memory expected!"))
			end
		end
		else begin
			if (expected_elip_reads.size() > 0) begin
				shortint data = expected_elip_reads.pop_front();
				shortint address = read_addresses.pop_front();
				if (t.data_read != data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data read via ELIP! Expected %04h but got %04h", data, t.data_read))
				end
				if ((t.address < base_address) || (t.address > base_address + size)) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address out of range! Got %04h but should be inside %04h .. %04h", t.address,  base_address , base_address + size ))
				end
				if (t.address != address) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Address is not correct! Got %04h but expected %04h ", t.address,  address))
				end
			end
			else begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("No read access to buffer memory expected!"))
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
		if (read_addresses.size()>0) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Not all addresses read are also read on ELIP! %0d remaining", read_addresses.size()))
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
