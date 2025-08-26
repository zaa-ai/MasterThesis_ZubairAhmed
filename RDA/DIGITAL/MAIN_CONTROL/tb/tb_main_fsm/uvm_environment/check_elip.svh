/**
 * Class: check_service
 * 
 * Class for register write accesses from command buffer
 */
class check_elip  extends uvm_scoreboard;
	`uvm_component_utils(check_elip)
	
	uvm_analysis_imp_elip_writer	#(elip_tr, 	check_elip)  elip_export;
	uvm_analysis_imp_elip_register	#(elip_tr, 	check_elip)  elip_register_export;
	
	typedef struct packed unsigned {
		data_t	address;
		data_t	data;
	} elip_access_t;
	
	protected	otp_address_t	otp_address_to_read;
	
	protected elip_access_t expected_elip_writes[$];
	
	protected int	error_count;
	
	protected logic [11:0] otp[0:4095];
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		elip_export = new("elip_export", this);
		elip_register_export = new("elip_register_export", this);
	endfunction
	
	function void write_elip_writer(elip_tr t);
		if (t.write == 1'b1) begin
			if (expected_elip_writes.size() > 0) begin
				elip_access_t expected = expected_elip_writes.pop_front();
				if (t.address != expected.address) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong address used for ELIP write! Expected %04h but got %04h", expected.address, t.address))
				end
				if (t.data_write != expected.data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Wrong data written to ELIP! Expected %04h but got %04h", expected.data, t.data_write))
				end
			end
			else begin
				error_count++;
				`uvm_error(this.get_type_name(), $sformatf("No access to ELIP expected! address=0x%4h, data=0x%4h", t.address, t.data_write))
			end
		end
		else begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("No read access expected at all!"))
		end
	endfunction
	
	function void write_elip_register(elip_tr t);
		case (t.address) 
			ADDR_OTP_CTRL_OTP_READ_ADDRESS : begin
				if (t.write == 1'b1) begin
					OTP_READ_ADDRESS_t	value = t.data_write;
					otp_address_to_read = value.ADDR;
				end
				else begin
					OTP_READ_ADDRESS_t	value = t.data_read;
					if (value.ADDR != otp_address_to_read) begin
						error_count++;
						`uvm_error(this.get_type_name(), $sformatf("Read unexpected address at ADDR_OTP_CTRL_OTP_READ_ADDRESS! Expected %4h, but got %4h", value.ADDR, otp_address_to_read))
					end
				end
			end
			ADDR_OTP_CTRL_OTP_READ_VALUE : begin
				if (t.write == 1'b0) begin
					OTP_READ_VALUE_t	value = t.data_read;
					if ({value.ECC, value.VALUE} != otp[otp_address_to_read]) begin
						error_count++;
						`uvm_error(this.get_type_name(), $sformatf("Read unexpected data at addresss %4h! Expected %4h, but got %4h", otp_address_to_read, {value.ECC, value.VALUE}, otp[otp_address_to_read]))
					end
				end
			end
		endcase
	endfunction
	
	protected function void check_data();
		if (expected_elip_writes.size()>0) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Not all writes done on ELIP! %0d remaining", expected_elip_writes.size()))
		end
	endfunction
	
	function void initialize(string otp_file_name);
		expected_elip_writes.delete();
		set_otp_data(otp_file_name);
		for (shortint unsigned ram_address = BASE_ADDR_RAM; ram_address < (BASE_ADDR_RAM +SIZE_RAM); ram_address+=16'd1) begin
			elip_access_t ram_row;
			ram_row.address = data_t'(ram_address);
			ram_row.data = data_t'(0);
			expected_elip_writes.push_back(ram_row);
		end
		otp_address_to_read = '0;
		error_count = 0;
	endfunction
	
	function void expect_no_access();
		expected_elip_writes.delete();
	endfunction
	
	function int get_error_count();
		check_data();
		return error_count;
	endfunction
	
	function void set_otp_data(string file_name);
		int otp_address;
		shortint address, data;
		$readmemh(file_name, otp);
		for(otp_address=0; otp_address<4095; otp_address++) begin
			address[15:8] = otp[otp_address][7:0]; 
			otp_address++;
			address[7:0] = otp[otp_address][7:0]; 
			if (address == 0) break;
			else begin
				elip_access_t	otp_write_to_elip;
				otp_address++;
				data[15:8] = otp[otp_address][7:0]; 
				otp_address++;
				data[7:0] = otp[otp_address][7:0];
				otp_write_to_elip.address = address;
				otp_write_to_elip.data = data;
				expected_elip_writes.push_back(otp_write_to_elip);
			end
		end
	endfunction
	
endclass
