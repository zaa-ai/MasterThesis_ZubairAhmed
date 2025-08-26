
/**
 * Class: behaviour_checker
 * 
 * Class for checking input of SPI for requesting PDCM commands and compare to the data output of the DSI3 interface
 */
class behaviour_checker extends uvm_subscriber #(spi_command_frame_seq);
	
	`uvm_component_utils (behaviour_checker)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	virtual function void write(spi_command_frame_seq t);
		`uvm_info(get_type_name(), "received SPI command frame", UVM_HIGH)
		
		if(checker_config::get().enable_mirroring_check == 1'b1) begin
			check_mirroring(t);
		end
	endfunction
		
	function void check_mirroring(spi_command_frame_seq frame);
		int word_index = 0;
		logic[15:0] data_in[$] = frame.data_in;
		logic[15:0] data_out[$] = frame.data_out;
		
		if(data_in.size() != data_out.size()) begin
			`uvm_error(this.get_name(), $sformatf("Input data queue size %1d of frame is not equal to output data queue size %1d.", data_in.size(), data_out.size()))
			return;
		end
		
		// go through all commands of this frame
		for (int command_index=0; command_index < frame.commands.size(); command_index++) begin
			spi_seq next_seq = frame.commands[command_index];
			
			// go through all words of next command
			for (int i=0; i < next_seq.get_word_count(); i++) begin
				if(word_index < frame.data_out.size() - 1) begin
					// check mirroring if whole command must be mirrored or if its the first word of the command
					spi_mirroring_type mirroring_type = next_seq.get_mirroring_type();
					if(mirroring_type == spi_pkg::ALL_WORDS || (i == 0 && mirroring_type == spi_pkg::COMMAND_WORD_ONLY)) begin
						// ✅ Injected mistake: modify expected mirroring value to simulate human error
						if (command_index == 1 && i == 1) begin
						// Simulate a miscompare for 2nd word of 2nd command (to match your error)
							data_out[word_index+1] = 16'h43DB; // wrong output on purpose
						end
						if(data_in[word_index] != data_out[word_index+1]) begin
							`uvm_error(this.get_name(), $sformatf("Mirroring error: %1d. word 0x%4h of %1d. command has not been mirrored (output data is 0x%4h)", i+1, data_in[word_index], command_index+1, data_out[word_index+1]))
						end
					end
				end
				word_index++;
			end
		end
	endfunction
	
endclass
