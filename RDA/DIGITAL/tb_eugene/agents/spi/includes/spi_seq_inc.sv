/**
 * SPI sequences. 
 */
class spi_seq extends spi_default_seq implements spi_command;
	
	rand logic[15:0] filler;      // random value to fill "don't care" bits of this sequence
	rand logic[15:0] data_in[$];  // data to be streamed out
		 logic[15:0] data_out[$]; // data streamed in
	
	// this flag is set if this sequence is the first sequence within a command frame (or if its a "stand alone" sequence) 
	bit is_first_of_frame = 1;
	// this flag is set if this sequence is the first sequence within a command frame (or if its a "stand alone" sequence) 
	bit is_last_of_frame = 1;
	
	
	// type of this SPI command (used for coverage definition)
	spi_cmd_type command_type;
	
	// default number of bits per SPI word
	int default_word_bit_count = 16;
	// word index to apply error word bit count	
	int error_word_index = -1;
	// error word bit count to be applied at error_word_index
	int error_word_bit_count = 16;
	
	static int word_index = -1;
	
	`uvm_object_utils_begin(spi_seq)
		`uvm_field_queue_int(data_in, UVM_DEFAULT | UVM_HEX | UVM_NORECORD)
		`uvm_field_queue_int(data_out, UVM_DEFAULT | UVM_HEX | UVM_NORECORD)
		`uvm_field_int(is_first_of_frame, UVM_DEFAULT)
		`uvm_field_int(is_last_of_frame, UVM_DEFAULT)
	`uvm_object_utils_end
	`uvm_declare_p_sequencer(spi_sequencer_t)
	
	/************************ Methods declarations ************************/
	function new(string name ="spi_seq");
		super.new(name);
		cov_spi_command_type = new();
	endfunction
  
	/************************ constraints ************************/
		
	covergroup cov_spi_command_type;
		option.per_instance = 0;
		coverpoint command_type;
	endgroup
	
	/************************ User defined methods declarations ************************/
	virtual task body();
		spi_config _config;
		_config = get_config();
		
		data_in.delete();
		data_out.delete();
		
		if(is_first_of_frame == 1'b1 && _config.csb_handler.falling_csb_at_frame_start() == 1'b1) begin
			word_index = -1;
			falling_csb();
		end
			
		for (int i=0; i<get_word_count(); i++) begin
			logic[15:0] word = get_word(i);
			word_index++;
			`uvm_create_on (req, p_sequencer)
			req.tr_type = spi_pkg::SPI_DATA;
			req.data_in = word;
			req.bit_count = (i == error_word_index) ? error_word_bit_count : default_word_bit_count;
			req.word_index = word_index;
			req.set_name("spi-data");
			`uvm_send (req)		
			
			data_in.push_back(req.data_in);
			data_out.push_back(req.data_out);
			
			if(_config.csb_handler.csb_after_word(word_index) == 1'b1 && (!is_last_of_frame || i < get_word_count() - 1)) begin
				rising_csb();
				falling_csb();
			end
		end
		
		if(is_last_of_frame == 1'b1 && _config.csb_handler.rising_csb_at_frame_end() == 1'b1) begin
			rising_csb();
		end
	endtask : body
	
	virtual function spi_config get_config();
		spi_sequencer sequencer;
		if($cast(sequencer, m_sequencer) != 1) `uvm_error(get_type_name(), "there seems to be a wrong type of sequencer, cast to spi_sequencer failed")
		return sequencer.m_config;
	endfunction
	
	virtual task falling_csb();
		`uvm_create_on (req, p_sequencer)
		req.tr_type = spi_pkg::SPI_START;
		req.set_name("spi-start");
		req.data_in = 16'hxxxx;
		req.data_out = 16'hxxxx;
		req.word_index = word_index;
		req.bit_count = 0;
		`uvm_send (req)	
	endtask
	
	virtual task rising_csb();
		`uvm_create_on (req, p_sequencer)
		req.tr_type = spi_pkg::SPI_END;
		req.set_name("spi-end");
		req.data_in = 16'hxxxx;
		req.data_out = 16'hxxxx;
		req.word_index = -1;
		req.bit_count = 0;
		`uvm_send (req)	
	endtask
	
	virtual function void sample_cov();
		command_type = get_command_code();
		cov_spi_command_type.sample();
	endfunction
	
	virtual function spi_tr create_transaction(spi_sequencer_t sequencer);
		`uvm_create_on (req, sequencer)
		return req;
	endfunction
			
	virtual function spi_cmd_type get_command_code();
		`uvm_fatal(get_type_name(), "get_command_code() function must be overridden by subclass")
		return CMD_STATUS_READ;
	endfunction
	
	virtual function bit starts_with(logic[15:0] word);
		return word[15:12] == get_command_code();
	endfunction
			
	virtual function int get_word_count();
		return 1;
	endfunction
	
	virtual function spi_mirroring_type get_mirroring_type();
		return spi_pkg::ALL_WORDS;
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		int word_count = get_word_count();
		// skip if there is not enough incoming data
		if(word_count > data_in.size() || word_count > data_out.size()) begin
			return 1'b0;
		end
		this.data_in.delete();
		this.data_out.delete();
		// copy in/out words
		for (int i=0; i<word_count; i++) begin
			this.data_in.push_back(data_in[i]);
			this.data_out.push_back(data_out[i]);
		end
		filler = data_in[0];
		return 1'b1;
	endfunction
	
	virtual function logic[15:0] get_word(int index);
		logic[15:0] cmd = filler;
		cmd[15:12] = get_command_code();
		return cmd;
	endfunction
	
	virtual function void do_record(uvm_recorder recorder);
		super.do_record(recorder);
		`uvm_record_field(" command", convert2string())
		`uvm_record_field(" data_in", queue_to_string(data_in))
		`uvm_record_field("data_out", queue_to_string(data_out))
	endfunction : do_record
			
	protected virtual function string queue_to_string(logic[15:0] queue[$]);
		string temp_string = "";
		for (int i=0; i<queue.size(); i++) begin
			temp_string = {temp_string, $sformatf("%4h ", queue[i])};
		end
		return temp_string;
	endfunction
	
endclass : spi_seq

`include "sequences/spi_master_register_seq.svh"
`include "sequences/spi_dsi_command_seq.svh"

`include "data/spi_dsi_data_packet.svh"
`include "data/spi_pdcm_frame_header.svh"

`include "sequences/spi_any_command_seq.svh"
`include "sequences/spi_reset_seq.svh"
`include "sequences/spi_read_status_seq.svh"
`include "sequences/spi_read_master_register_seq.svh"
`include "sequences/spi_write_master_register_seq.svh"
`include "sequences/spi_crm_seq.svh"
`include "sequences/spi_upload_tdma_packet_seq.svh"
`include "sequences/spi_validate_tdma_scheme_seq.svh"
`include "sequences/spi_discovery_mode_seq.svh"
`include "sequences/spi_read_dsi_data_seq.svh"
`include "sequences/spi_read_crm_data_packets_seq.svh"
`include "sequences/spi_read_pdcm_frame_seq.svh"
`include "sequences/spi_tx_crc_request_seq.svh"
`include "sequences/spi_dsi_wait_seq.svh"
`include "sequences/spi_pdcm_seq.svh"
`include "sequences/spi_sync_dsi_channels_seq.svh"
`include "sequences/spi_clear_dsi_command_queue_seq.svh"
`include "sequences/spi_clear_dsi_data_buffers_seq.svh"
`include "sequences/spi_measure_quiescent_current_seq.svh"
`include "sequences/spi_command_frame_seq.svh"

`include "components/behaviour_checker.svh"
`include "components/spi_protocol_listener.svh"
`include "spi_seq_factory.svh"
`include "components/spi_frame_factory.svh"
`include "components/spi_frame_factory_with_single_command.svh"
