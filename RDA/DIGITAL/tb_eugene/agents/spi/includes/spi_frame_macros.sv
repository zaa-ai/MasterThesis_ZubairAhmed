/************************ SPI Command Macros ************************/
	
	// declare and create a new spi_command_frame
	`define spi_frame_begin begin \
			spi_command_frame_seq frame; \
			`uvm_create_on(frame, m_spi_agent.m_sequencer)
	
	// send this frame
	`define spi_frame_end		`uvm_send(frame) \
		end

	// send this frame and check spi status word of this frame
	`define spi_frame_end_with_status(_flags_)	`uvm_send(frame) \
			begin \
				flags_container #(spi_status_word_flags) flags = new(); \
				flags.set_flags(_flags_); \
				void'(frame.status.check_flags_are_equal(flags, $sformatf("Unexpected SPI status word flags"))); \
			end \
		end
						
						
	// create and randomize a new SPI sequence of given type and add it to an existing frame
	`define spi_frame_create(_type_, _constraints_)	begin \
			_type_ _``_type_; \
			`uvm_create_on(_``_type_, m_spi_agent.m_sequencer) \
			if(_``_type_.randomize() with {_constraints_} != 1) `uvm_error(this.get_name(), "randomization failed") \
			frame.add_command(_``_type_); \
		end
										
	// randomize an existing SPI sequence and add it to an existing frame													
	`define spi_frame_send(_name_, _constraints_)  begin \
			`uvm_create(_name_) \
			if(_name_.randomize() with {_constraints_} != 1) `uvm_error(this.get_name(), "randomization failed") \
			frame.add_command(_name_); \
		end
	
	/**
	 * Create, randomize and send a base_dsi_master_seq. 
	 */												
	`define	create_and_send(_seq_) begin \
			_seq_ _``_seq_; \
			`uvm_do(_``_seq_) \
		end	
							
	`define	create_and_send_with(_seq_, _constraints_) begin \
			_seq_ _``_seq_; \
			`uvm_do_with(_``_seq_, {_constraints_}) \
		end	

	/**
	 * Upload a given TDMA scheme. 
	 */												
	`define	upload_tdma_scheme_with(_scheme_, _constraints_) begin \
			upload_tdma_scheme_seq upload_seq; \
			`uvm_create(upload_seq)	\
			if(upload_seq.randomize() with {_constraints_} != 1) `uvm_error(this.get_name(), "randomization failed") \
			upload_seq.scheme = _scheme_; \
			`uvm_send(upload_seq) \
		end	