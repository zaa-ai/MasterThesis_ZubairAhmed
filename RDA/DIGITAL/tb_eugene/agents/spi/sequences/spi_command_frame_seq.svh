/**
 * Class: spi_command_frame_seq
 * 
 * A SPI command frame is a collection of multiple SPI commands.
 */
class spi_command_frame_seq extends spi_seq;
	
	rand spi_seq commands[$];
	logic[15:0] crc_data_in[$]; // data streamed in for next mosi crc calculation
	
	spi_status_word	status;
	
	`uvm_object_utils_begin (spi_command_frame_seq)
		`uvm_field_object(status, UVM_DEFAULT )
	`uvm_object_utils_end
	
	/************************ constraints ************************/
	
	
	/************************ Methods declarations ************************/
	function new(string name = "SPI command frame");
		super.new(name);
		status = new();
	endfunction
	
	virtual function void sample_cov();
		status.sample_cov();
	endfunction
			
	protected function string get_crc_string(logic crc);
		if (crc === 1'b1)
			return "CRC OK";
		if (crc === 1'b0)
			return "CRC NOK";
		if (crc === 1'bx)
			return "CRC not set";
	endfunction		
		
	function void add_command(spi_seq cmd);
		spi_tx_crc_request_seq tx_crc;
		spi_reset_seq reset_seq;
		
		// check for "SPI frame CRC command"
		if($cast(tx_crc, cmd) == 1) begin
			update_frame_data_in();
			if(tx_crc.mosi_crc_enable == 1) begin
				crc_data_in.push_back(tx_crc.get_word(0)); // include command word to CRC
				tx_crc.mosi_crc = crc_calculation_pkg::spi_calculate_crc(tx_crc.mosi_crc_correct, crc_data_in);
			end
			crc_data_in.delete();
		end
		// check for "SPI Reset command"
		else if($cast(reset_seq, cmd) == 1 && reset_seq.incomplete == 1'b0) begin
			crc_data_in.delete();
		end
		// all other commands
		else begin
			for(int j=0; j < cmd.get_word_count(); j++) begin
				crc_data_in.push_back(cmd.get_word(j));
			end
		end
		
		cmd.is_first_of_frame = (commands.size() == 0);
		
		if(commands.size() > 0) begin
			commands[commands.size()-1].is_last_of_frame = 1'b0;
		end
		cmd.is_last_of_frame = 1'b1;
		
		commands.push_back(cmd);
	endfunction
			
	virtual task body();
		data_in.delete();
		data_out.delete();
		p_sequencer.lock(this);
		
		for (int i=0; i<commands.size(); i++) begin
			spi_seq command = commands[i];
			`uvm_send (command);
			update_data(command);
		end
		
		p_sequencer.unlock(this);
		update_status();
		update_sequences();
	endtask
	
	function void update_frame_data_in();
		data_in.delete();
		foreach(commands[i]) begin
			for(int j=0; j < commands[i].get_word_count(); j++) begin
				data_in.push_back(commands[i].get_word(j));
			end
		end
	endfunction
		
	function void update_data(spi_seq seq);
		for(int j=0; j < seq.data_in.size(); j++) begin
			data_in.push_back(seq.data_in[j]);
			data_out.push_back(seq.data_out[j]);
		end
	endfunction
	
	function void update_status();
		if(data_out.size() > 0) begin
			status.set(data_out[0]);
		end
	endfunction
	
	function void update_sequences();
		logic[15:0] temp_data_in[$] = data_in;
		logic[15:0] temp_data_out[$] = data_out;
		foreach(commands[i]) begin
			commands[i].create_from(temp_data_in, temp_data_out);
			// remove already converted words
			for (int j=0; j < commands[i].get_word_count(); j++) begin
				temp_data_in.pop_front();
				temp_data_out.pop_front();
			end
		end
	endfunction

	function void check_status_flags(spi_status_word_flags status_flags[$]);
		status.check_status_flags(status_flags);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("spi command frame (%0d commands)", commands.size());
	endfunction
			
endclass


