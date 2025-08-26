typedef enum { Error, withoutError } crc_error_inject_type_t;
//typedef enum { CRM, PDCM, IDLE } cmd_type_t;
typedef enum { RUN, HOLD } ctrl_t;

class ring_buffer_status extends uvm_report_object;
	protected int	free;
	protected int	valid_count;
	protected int	read_pointer;
	protected int	valid_pointer;
	protected int	write_pointer;
	protected simulation_logger logger;
	
	protected int size;
	protected int base_address;
	protected ral_regfile_ring_buffer_registers ring_buffer;
	
	function new (int base_address, ral_regfile_ring_buffer_registers ring_buffer, string name="");
		super.new(name);
		this.size = size;
		this.base_address = base_address;
		this.ring_buffer = ring_buffer;
		initialize();
	endfunction
	
	virtual function void initialize();
		if (logger == null)	logger = new("sim_logger");
		free = size - 1;
		valid_count = 0;
		read_pointer = 0;
		valid_pointer = 0;
		write_pointer = 0;
	endfunction
	
	virtual task get_current_status();
		get_register_value(ring_buffer.BUF_FREE,			free);
		get_register_value(ring_buffer.BUF_VALID_COUNT,		valid_count);
		get_register_value(ring_buffer.BUF_READ_POINTER,	read_pointer);  
		get_register_value(ring_buffer.BUF_VALID_POINTER,	valid_pointer);
		get_register_value(ring_buffer.BUF_WRITE_POINTER,	write_pointer);
		check_plausibility();
	endtask
	
	protected virtual task get_register_value(uvm_reg register, ref int value);
		uvm_status_e	status;
		uvm_reg_data_t read_value;
		register.read(status, read_value);
		value = read_value[31:0];
	endtask
	
	virtual task check_read_sequence(spi_read_master_register_seq	read_sequence);
		check_value(read_sequence.burst_data[0], free, "free");
		check_value(read_sequence.burst_data[1], valid_count, "valid_count");
		check_value(read_sequence.burst_data[2], read_pointer, "read_pointer");
		check_value(read_sequence.burst_data[3], valid_pointer, "valid_pointer");
		check_value(read_sequence.burst_data[4], write_pointer, "write_pointer");
		check_plausibility();
	endtask
	
	virtual task compare_buffer_registers();
		check_register(ring_buffer.BUF_FREE,			free);
		check_register(ring_buffer.BUF_VALID_COUNT,		valid_count);
		check_register(ring_buffer.BUF_READ_POINTER,	read_pointer);  
		check_register(ring_buffer.BUF_VALID_POINTER,	valid_pointer);
		check_register(ring_buffer.BUF_WRITE_POINTER,	write_pointer);
		check_plausibility();
	endtask
	
	virtual task check_register(uvm_reg register, uvm_reg_data_t expected_value); // FIXME: is the same as in base_dsi_master_seq
		uvm_reg_data_t	value;
		uvm_status_e	status;
		register.read(status, value);
		if (expected_value != value) begin
			`uvm_error(this.get_name(), $sformatf("%s is not set correctly. Got %4h but expected %4h (%s)", register.get_name() , value, expected_value, register.get_full_name()))
			logger.log_sim_check(register.get_name(), .status("FAIL"));
		end
		else begin
			logger.log_sim_check(register.get_name(), .status("PASS"));
		end
	endtask
	
	protected virtual function void check_value(int value, int expected_value, string text);
		if (value != expected_value)
			`uvm_error(this.get_name(), $sformatf("Value of %s is not correct! Exp. 0x%4h but got 0x%4h", text, expected_value, value))
	endfunction
	
	virtual function void write(int words);
		if (free > words) begin
			write_pointer = trim(write_pointer + words);
			calculate_free();
		end
	endfunction
	
	virtual function void validate();
		valid_pointer = write_pointer;
		calculate_valid_count();
	endfunction
	
	virtual function void invalidate();
		write_pointer = valid_pointer;
		calculate_free();
	endfunction
	
	virtual function void read(int words);
		if (valid_count < words) begin
			words = valid_count;
		end
		read_pointer = trim(read_pointer + words);
		calculate_free();
		calculate_valid_count();
	endfunction
	
	virtual function void check_plausibility();
		check_pointer(read_pointer,  "read");
		check_pointer(write_pointer, "write");
		check_pointer(valid_pointer, "valid");
	endfunction
	
	protected virtual function void check_pointer(int _pointer, string pointer_name);
		if((_pointer > base_address + size) || (_pointer < base_address))	
			`uvm_error(this.get_name(), $sformatf("pointer %s is outside of its expected range. Base address=0x%4h, buffer size=0x%4h, pointer value=0x%4h", pointer_name, base_address, size, _pointer))
	endfunction
	
	protected virtual function void calculate_free();
		if (read_pointer > write_pointer)	
			free = read_pointer - write_pointer - 1;
		else
			free = size - (write_pointer - read_pointer) - 1;
	endfunction
	
	protected virtual function void calculate_valid_count();
		if (valid_pointer >= read_pointer)
			valid_count = valid_pointer - read_pointer;
		else
			valid_count = size - (read_pointer - valid_pointer);
	endfunction
	
	protected virtual function int trim(int value);
		int trimmed_value = value;
		if (value >= base_address + size) trimmed_value -= size;
		return trimmed_value;
	endfunction
	
	virtual function void randomize_with_addresses(spi_read_master_register_seq read_seq);
		logic[11:0] addresses[$];
		addresses.push_back(shortint'(ring_buffer.BUF_FREE.get_address()));
		addresses.push_back(shortint'(ring_buffer.BUF_VALID_COUNT.get_address()));
		addresses.push_back(shortint'(ring_buffer.BUF_READ_POINTER.get_address()));
		addresses.push_back(shortint'(ring_buffer.BUF_VALID_POINTER.get_address()));
		addresses.push_back(shortint'(ring_buffer.BUF_WRITE_POINTER.get_address()));
		if(read_seq.randomize() with {address == 0; burst_addresses.size() == addresses.size(); foreach(burst_addresses[i]) burst_addresses[i] ==  addresses[i];} != 1) 
			`uvm_error(this.get_type_name(), "randomization failed")
	endfunction
	
endclass

class dsi_crm_data_buffer_status extends ring_buffer_status;
	
	function new (int base_address, ral_regfile_ring_buffer_registers buffer_reg, string name = "");
		super.new(base_address, buffer_reg, name);
		this.size = project_pkg::SIZE_DSI_CRM_BUF;
	endfunction
	
endclass

class dsi_pdcm_data_buffer_status extends ring_buffer_status;
    
    function new (int base_address, ral_regfile_ring_buffer_registers buffer_reg, string name = "");
        super.new(base_address, buffer_reg, name);
        this.size = project_pkg::SIZE_DSI_PDCM_BUF;
    endfunction
    
endclass

class dsi_cmd_buffer_status extends ring_buffer_status;
	
	function new (int base_address, ral_regfile_ring_buffer_registers buffer_reg, string name = "");
		super.new(base_address, buffer_reg, name);
		this.size = project_pkg::SIZE_DSI_CMD_BUF;
	endfunction
	
endclass

class spi_cmd_buffer_status extends ring_buffer_status;
	
	function new (ral_regfile_ring_buffer_registers buffer_reg, string name="");
		super.new(project_pkg::BASE_ADDR_SPI_CMD_BUF, buffer_reg, name);
		this.size = project_pkg::SIZE_SPI_CMD_BUF;
	endfunction
	
endclass

`include "spi_cmd_buffer_status_seq.svh"
`include "dsi_cmd_buffer_status_seq.svh"
`include "dsi_pdcm_data_buffer_status_seq.svh"
`include "dsi_crm_data_buffer_status_seq.svh"

class ring_buffer_status_seq extends base_dsi_master_seq;
                         
	`uvm_object_utils(ring_buffer_status_seq)
    

	function new(string name = "");
		super.new("ring_buffer_status");
	endfunction : new

	virtual task run_tests();
		log_sim_description("Testcase for ring buffer status registers", LOG_LEVEL_TOP);
		
		check_spi_command_buffer_status();
		check_dsi_command_buffer_status();
		check_dsi_pdcm_data_buffer_status();
        check_dsi_crm_data_buffer_status();
		
	endtask
	
	virtual task check_spi_command_buffer_status();
		log_sim_description("check SPI command buffer status registers", 1);
		`create_and_send_with(spi_cmd_buffer_status_seq, crc_error == 1'b0;)
		`create_and_send_with(spi_cmd_buffer_status_seq, crc_error == 1'b1;)
		repeat(10) begin
			`create_and_send(spi_cmd_buffer_status_seq);
		end
		reset();
	endtask
	
	virtual task reset(string otp_file_name="", time rfc_timeout = 5ms);
		#100us;
		super.reset(otp_file_name, rfc_timeout);
		#500us;
	endtask
	
	virtual task check_dsi_command_buffer_status();
		log_sim_description("check DSI command buffer status registers", 1);
		repeat(30) begin
			`create_and_send(dsi_cmd_buffer_status_seq)
		end
		reset();
	endtask
	
	virtual task check_dsi_pdcm_data_buffer_status();
		log_sim_description("check DSI pdcm data buffer status registers", 1);
		repeat(30) begin
			`create_and_send(dsi_pdcm_data_buffer_status_seq)
		end
		reset();
    endtask
    
    virtual task check_dsi_crm_data_buffer_status();
        log_sim_description("check DSI crm data buffer status registers", 1);
        repeat(30) begin
            `create_and_send(dsi_crm_data_buffer_status_seq)
        end
        reset();
    endtask
    
endclass
