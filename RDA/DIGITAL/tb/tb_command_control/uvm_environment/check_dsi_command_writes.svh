class check_clearing extends uvm_report_object;
	virtual dsi_logic_if vif;

	protected	event start;
	protected	bit triggered;
	protected	int channel;


	function new(string name = "check_clearing");
		super.new(name);
		triggered = 1'b1;
	endfunction

	function void start_trigger();
		triggered = 1'b0;
		fork
			run_check();
		join_none
		->start;
	endfunction

	function bit has_triggered();
		if (!triggered) begin
			`uvm_error(this.get_type_name(), $sformatf("Clearing %s did not trigger for channel %1d", this.get_name(), channel))
		end
		return triggered;
	endfunction

	protected task run_check();
		@(posedge vif.D[channel]) triggered = 1'b1;
	endtask

	function void initialize();
		triggered = 1'b1;
	endfunction

	virtual function void set_channel(int channel);
		this.channel = channel;
	endfunction

endclass

/**
 * Class: check_service
 *
 * Class for register write accesses from command buffer
 */
class check_dsi_command_writes  extends uvm_scoreboard;
	`uvm_component_utils(check_dsi_command_writes)

	uvm_analysis_imp_frame_writer	#(spi_command_frame_seq,	check_dsi_command_writes)	frame_export;
	uvm_analysis_imp_buffer_writer	#(buffer_writer_tr,			check_dsi_command_writes)	buffer_export;

	protected buffer_writer_tr expected_buffer_writes[$];

	protected int	error_count;
	protected int channel;
	protected	bit enabled;
	check_clearing _check_crm_data_buffer_clearing, _check_pdcm_data_buffer_clearing, _check_command_buffer_clearing;

	function new(string name, uvm_component parent);
		super.new(name, parent);
		frame_export = new("frame_export", this);
		buffer_export = new("buffer_export", this);
		enabled = 1'b1;
		_check_crm_data_buffer_clearing = new("crm_data_buffer");
		_check_pdcm_data_buffer_clearing = new("pdcm_data_buffer");
		_check_command_buffer_clearing = new("command_buffer");
	endfunction

	virtual function void write_frame_writer(spi_command_frame_seq t);
		if (enabled == 1'b1) begin
			bit validation_needed = 1'b0;
			int command_index, data_index;
			for (command_index = 0; command_index < t.commands.size(); command_index++) begin
				case (t.commands[command_index].get_command_code())
					CMD_CRM, CMD_PDCM, CMD_DSI_DISCOVERY_MODE,
					CMD_DSI_WAIT,
					CMD_DSI_SYNC, CMD_UPLOAD_TDMA: begin
						spi_dsi_command_seq dsi_seq;
						if ($cast(dsi_seq, t.commands[command_index])) begin
							if (dsi_seq.channel_bits[channel]) begin
								for (data_index = 0; data_index<t.commands[command_index].get_word_count(); data_index++) begin
									shortint	ecc;
									buffer_writer_tr	buffer_t = new();
									buffer_t.action = BUFFER_WRITE;
									buffer_t.data = t.commands[command_index].get_word(data_index);
									ecc = DWF_ecc_gen_chkbits(16,6, t.commands[command_index].get_word(data_index));
									buffer_t.ecc = ecc;
									expected_buffer_writes.push_back(buffer_t);
									validation_needed = 1'b1;
								end
							end
						end
						else begin
							`uvm_error(this.get_full_name(), $sformatf("Casting error from %s to %s", t.commands[command_index].get_type_name(), "spi_dsi_command_seq"))
						end
					end
					CMD_DSI_CLEAR_QUEUE: begin
						spi_dsi_command_seq dsi_seq;
						if ($cast(dsi_seq, t.commands[command_index])) begin
							if (dsi_seq.channel_bits[channel]) begin
								shortint	ecc;
								buffer_writer_tr	buffer_t = new();
								buffer_t.action = BUFFER_CLEAR;
								buffer_t.data = t.commands[command_index].get_word(data_index);
								ecc = DWF_ecc_gen_chkbits(16,6, t.commands[command_index].get_word(data_index));
								buffer_t.ecc = ecc[5:0];
								expected_buffer_writes.push_back(buffer_t);
								validation_needed = 1'b0;
								_check_command_buffer_clearing.start_trigger();
							end
						end
						else begin
							`uvm_error(this.get_full_name(), $sformatf("Casting error from %s to %s", t.commands[command_index].get_type_name(), "spi_dsi_command_seq"))
						end
					end
					CMD_DSI_CLEAR_BUF : begin
						spi_clear_dsi_data_buffers_seq clear_data_seq;
						if ($cast(clear_data_seq, t.commands[command_index])) begin
							if (clear_data_seq.channel_bits[channel]) begin
                                if (clear_data_seq.crm_buffer) begin
								    _check_crm_data_buffer_clearing.start_trigger();
                                end
                                if (clear_data_seq.pdcm_buffer) begin
								    _check_pdcm_data_buffer_clearing.start_trigger();
                                end
							end
						end
						else begin
							`uvm_error(this.get_full_name(), $sformatf("Casting error from %s to %s", t.commands[command_index].get_type_name(), "spi_dsi_command_seq"))
						end
					end
				endcase
			end
			if (validation_needed) begin
				buffer_writer_tr	buffer_t = new();
				buffer_t.action = BUFFER_VALIDATE;
			end
		end
	endfunction

	`define expected_address_min 'h1000
	`define expected_address_max 'h1100

	virtual function void set_channel(int channel);
		this.channel = channel;
		_check_crm_data_buffer_clearing.set_channel(channel);
		_check_pdcm_data_buffer_clearing.set_channel(channel);
		_check_command_buffer_clearing.set_channel(channel);
	endfunction

	virtual function void write_buffer_writer(buffer_writer_tr t);
		buffer_writer_tr expected = expected_buffer_writes.pop_front();
		if (expected == null) begin

		end
		else begin
			default_comparer comparer = new();
			case (t.action)
				BUFFER_VALIDATE,BUFFER_WRITE, BUFFER_CLEAR: begin
					void'(t.compare(expected, comparer));
				end
				BUFFER_WRITE_FIRST: begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("no writing of first address expected!"))
				end
			endcase
		end
	endfunction

	protected virtual function void check_data();
		if (expected_buffer_writes.size()>0) begin
			error_count++;
			`uvm_error(this.get_full_name(), $sformatf("Not all command writes done! %0d remaining", expected_buffer_writes.size()))
		end
	endfunction

	virtual function void initialize();
		_check_crm_data_buffer_clearing.initialize();
		_check_pdcm_data_buffer_clearing.initialize();
		_check_command_buffer_clearing.initialize();
		expected_buffer_writes.delete();
		error_count = 0;
	endfunction

	virtual function int get_error_count();
		check_data();
		void'(_check_crm_data_buffer_clearing.has_triggered());
		void'(_check_pdcm_data_buffer_clearing.has_triggered());
		void'(_check_command_buffer_clearing.has_triggered());
		return error_count;
	endfunction

	virtual function void set_enable(bit enable);
		if (enable == 1'b0) begin
			buffer_writer_tr t = new();
			t.action = BUFFER_CLEAR;
			expected_buffer_writes.push_back(t);
			enabled = 1'b0;
		end
		else begin
			enabled = 1'b1;
		end
	endfunction

endclass
