/**
 * Class: command_buffer_creator
 *
 * TODO: Add class documentation
 */
class command_buffer_creator extends uvm_subscriber #(spi_command_frame_seq);

	`uvm_component_utils (command_buffer_creator)

	uvm_analysis_port		#(buffer_writer_tr)		 buffer_port;

	function new(string name = "command_buffer_creator", uvm_component parent);
		super.new(name, parent);
		buffer_port = new("spi_command_frame_port", this);
	endfunction

	virtual function void write(spi_command_frame_seq t);
		bit	buffer_validated = 1'b1;
		for (int command_index=0; command_index<t.commands.size(); command_index++) begin
			spi_seq command = t.commands[command_index];
			if (command.get_type_name() == spi_tx_crc_request_seq::type_name) begin
				spi_tx_crc_request_seq crc_seq;
				if ($cast(crc_seq, command)) begin
					validate_buffer(crc_seq.mosi_crc_correct);
					buffer_validated = 1'b1;
				end
				else begin
					`uvm_error(this.get_type_name(), "Casting to crc_seq failed!")
				end
			end
			else begin
				case(command.get_command_code())
					CMD_REG_WRITE         	,
					CMD_DSI_CLEAR_QUEUE   	,
					CMD_DSI_CLEAR_BUF     	,
					CMD_DSI_DISCOVERY_MODE  ,
					CMD_UPLOAD_TDMA         ,
					CMD_CRM		   			,
					CMD_PDCM			   	,
					CMD_DSI_WAIT          	,
					CMD_DSI_SYNC: begin
						for(int data_index=0; data_index < command.data_in.size(); data_index++) begin
							create_and_write_buffer_transaction(command.data_in[data_index]);
						end
						buffer_validated = 1'b0;
					end
				endcase
			end
		end
		if (!buffer_validated) begin
			validate_buffer(1'b0);
		end
	endfunction

	virtual function void create_and_write_buffer_transaction(int data);
		shortint ecc;
		buffer_writer_tr	new_transaction = new();
		ecc = DWF_ecc_gen_chkbits(16,6,data);
		void'(this.begin_tr(new_transaction, "write_buffer"));
		new_transaction.data = data;
		new_transaction.ecc = ecc;
		new_transaction.action = BUFFER_WRITE;
		void'(this.end_tr(new_transaction));
		`uvm_info(this.get_type_name(), new_transaction.convert2string(), UVM_DEBUG)
		buffer_port.write(new_transaction);
	endfunction

	virtual function void validate_buffer(bit valid);
		buffer_writer_tr	new_transaction = new();
		void'(this.begin_tr(new_transaction, "validate_buffer"));
		new_transaction.data = 16'hxxxx;
		if (valid == 1'b1)
			new_transaction.action = BUFFER_VALIDATE;
		else
			new_transaction.action = BUFFER_INVALIDATE;
		void'(this.end_tr(new_transaction));
		`uvm_info(this.get_type_name(), new_transaction.convert2string(), UVM_DEBUG)
		buffer_port.write(new_transaction);
    endfunction
    
    virtual function void reset_buffer();
		buffer_writer_tr	new_transaction = new();
        validate_buffer(1'b0);
//		void'(this.begin_tr(new_transaction, "clear_buffer"));
//		new_transaction.data = 16'hxxxx;
//		new_transaction.action = BUFFER_INVALIDATE;
//		void'(this.end_tr(new_transaction));
//		`uvm_info(this.get_type_name(), new_transaction.convert2string(), UVM_DEBUG)
//		buffer_port.write(new_transaction);
    endfunction

endclass
