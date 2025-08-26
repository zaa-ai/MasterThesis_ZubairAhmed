/**
 * Class: frame_facade
 * 
 * Facade class to start a buffer transaction from a SPI frame	
 */
class frame_facade extends spi_frame_factory;
	
	buffer_writer_sequencer_t	sequencer;
	
	uvm_analysis_port #(spi_command_frame_seq) frame_port;

	function new(string name="frame_facade");
		super.new(name);
		// @SuppressProblem -type uvm_tlm_port_without_parent_or_imp -count 1 -length 1
		frame_port = new("frame_port", null);
	endfunction
	
	virtual task start_random_queueing_frame();
		spi_command_frame_seq seq = spi_frame_factory::create_random_frame_with_queue_commands(null);
		start_me(seq);
	endtask
	
	virtual task start_this(spi_command_frame_seq seq);
		start_me(seq);
	endtask
	
	protected virtual task start_me(spi_command_frame_seq seq);
		buffer_write_seq buffer = new();
		int command_index, data_index;
		for (command_index = 0; command_index < seq.commands.size(); command_index++) begin
			for (data_index = 0; data_index<seq.commands[command_index].get_word_count(); data_index++)
				buffer.data.push_back(seq.commands[command_index].get_word(data_index));
		end
		buffer.valid = 1'b1;
		buffer.do_validation = 1'b1;
		frame_port.write(seq);
		foreach (seq.commands[i])
			`uvm_info(this.get_type_name(), $sformatf("starting %s", seq.commands[i].convert2string()) , UVM_DEBUG)
		
		buffer.start(sequencer);
	endtask

endclass


