/**
 * Class: check_service
 *
 * Class for checking SPI communication
 */
class check_service  extends uvm_subscriber #(spi_tr);
	`uvm_component_utils(check_service)

	protected int	error_count;
	logic[15:0]		spi_data_in[$];
	logic[15:0]		spi_data_out[$];
	bit				spi_incomplete[$];
	data_ecc_t		data_received;
	logic[15:0]		crc_in;
	logic[15:0]		crc_out;
	bit				command_pending[$];
	bit				incomplete;
	data_ecc_t		transmit_data[$];
	bit				transmit[$];
	logic[15:0]		status_words;

	function void write(spi_tr t);
		case (t.tr_type)
			SPI_DATA: begin
				spi_data_in.push_back(t.data_in);
				spi_data_out.push_back(t.data_out);
				spi_incomplete.push_back((t.bit_count < 16) ? 1'b1 : 1'b0);
				fork
					begin
						#5ns;
						check_data();
					end
				join_none
			end
			SPI_END: begin
				fork
					#5ns;
					check_incomplete();
				join_none
			end
		endcase
	endfunction

	protected function void check_data();
		check_received_data();
		check_transmitted_data_output();
		check_crc_in_calculation();
		check_crc_out_calculation();
		
		check_crc_output();
		check_status_word_output();
		
		// check resetting of queues spi_data_in, spi_data_out
	endfunction

	protected function void check_received_data();
		ecc_t  ecc;
		if (spi_data_in[$] != data_received.data) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Received a different word then it was sent via SPI! Received %04h but should be %04h", data_received, spi_data_in[$]))
		end
		else begin
			cg_spi_received_data.sample();
		end
		ecc = DWF_ecc_gen_chkbits(16,6,spi_data_in[$]);
		if (ecc !== (data_received.ecc)) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("ECC was not correctly calculated! Calculated %04h but should be %04h", data_received.ecc, DWF_ecc_gen_chkbits(16,6, spi_data_in[$])))
		end
	endfunction

	protected function void check_transmitted_data_output();
		if (transmit.size > 1) begin // first 2 words cannot be transmitted data
			if (transmit[0] == 1'b1) begin
				if (spi_data_out[$] !== transmit_data[0].data) begin
					error_count++;
					`uvm_error(this.get_type_name(), $sformatf("Transmitted data word is not output correctly! Data word output was %04h but exp. %04h", spi_data_out[$], transmit_data[0].data))
				end
				else begin
					cg_spi_transmitted_data.sample();
				end
			end
			void'(transmit.pop_front());
			void'(transmit_data.pop_front());
		end
		else begin
			
		end
	endfunction

	protected function void check_crc_in_calculation();
		logic[15:0] crc_from_spi_input;
		crc_from_spi_input = common_pkg::crc_ccitt_16(spi_data_in);
		if (crc_from_spi_input !== crc_in) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("CRC for input stream is different! CRC calculated is %04h while spi_core calculated %04h", crc_from_spi_input, crc_in))
		end
		else begin
			cg_spi_crc_in_calculation.sample();
		end
	endfunction
	
	protected function void check_crc_out_calculation();
		logic[15:0] crc_from_spi_output;
		crc_from_spi_output = common_pkg::crc_ccitt_16(spi_data_out);
		if (crc_from_spi_output != crc_out) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("CRC for input stream is different! CRC calculated is %04h while spi_core calculated %04h", crc_from_spi_output, crc_out))
		end
		else begin
			cg_spi_crc_out_calculation.sample();
		end
	endfunction

	protected function void check_crc_output();
//		for (int i=0; i< spi_data_in.size(); i++) begin
//			if (spi_data_in[i][15:12] == project_pkg::CRC_OUT) begin
//				if (command_pending[i] == 1'b0) begin
//					int index = i+1;
//					if (index < spi_data_out.size()) begin
//						if (spi_data_out[index] != crc_out[i]) begin
//							error_count++;
//							`uvm_error(this.get_type_name(), $sformatf("CRC is not output correctly! CRC is %04h but exp. %04h (index=%d)", spi_data_out[index], crc_out[index], index))
//							`uvm_info(this.get_type_name(), $sformatf("\ndata in      %p\ndata out     %p\ncrc output   %p\ncomman_pending%p", spi_data_in[i-2:i+2], spi_data_out[i-2:i+2], crc_out[i-2:i+2], command_pending[i-2:i+2]), UVM_LOW)
//						end
//						else begin
//							cg_spi_crc_output.sample();
//						end
//					end
//				end
//			end
//		end
	endfunction

	protected function void check_status_word_output();
//		check_status_word_output_first_word();
//		for (int i=0; i< spi_data_in.size(); i++) begin
			//FIXME: add checker!!
//			if (spi_data_in[i][15:12] == project_pkg::IC_STATUS) begin
//				if (command_pending[i] == 1'b0) begin
//					int index = index;
//					if (index < spi_data_out.size()) begin
//						if (spi_data_out[index] != status_words[index]) begin
//							error_count++;
//							`uvm_error(this.get_type_name(), $sformatf("Status word is not output correctly! Status word output was %04h but exp. %04h (index=%d)", spi_data_out[index], status_words[index], index))
//							`uvm_info(this.get_type_name(), $sformatf("\ndata in      %p\ndata out     %p\nStatus words %p\ncomman_pending%p", spi_data_in[i-2:i+2], spi_data_out[i-2:i+2], status_words[i-2:i+2], command_pending[i-2:i+2]), UVM_LOW)
//						end
//						else begin
//							cg_spi_status_word_output.sample();
//						end
//					end
//				end
//			end
//		end
	endfunction

	protected function void check_status_word_output_first_word();
		if (spi_data_out[0] != status_words) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("Status word is not output correctly! Status word output was %04h but exp. %04h (index=0)", spi_data_out[0], status_words[0]))
		end
		else begin
			cg_spi_status_word_at_first.sample();
		end
	endfunction

	protected function void check_incomplete();
		bit spi_incomplete_ored = 1'b0;
		foreach (spi_incomplete[i])
			spi_incomplete_ored |= spi_incomplete[i];
		if (incomplete != spi_incomplete_ored) begin
			error_count++;
			`uvm_error(this.get_type_name(), $sformatf("incomplete flag not set correctly! flag was %1b but exp. %1b", incomplete, spi_incomplete_ored))
		end
	endfunction

	function void initialize();
		data_received = '0;
		crc_in = '0;
		crc_out = '0;
		command_pending.delete();
		incomplete = '0;
		transmit.delete();
		transmit_data.delete();
		status_words = '0;
		error_count = 0;
	endfunction

	function void set_crc_in(logic[15:0] word);
		crc_in = word;
	endfunction

	function void set_crc_out(logic[15:0] word);
		crc_out = word;
	endfunction

	function void set_received_word(data_ecc_t word);
		data_received = word;
	endfunction

	function void set_transmitted_word(data_ecc_t word, bit is_to_be_send=1'b0);
		transmit_data.push_back(word);
		transmit.push_back(is_to_be_send);
	endfunction

	function void set_status_word(logic[15:0] word);
		status_words = word;
	endfunction

	function void set_command_pending_flag(bit flag);
		command_pending.push_back(flag);
	endfunction

	function void add_incomplete_flag(bit flag);
		incomplete = flag;
	endfunction

	function int get_error_count();
		return error_count;
	endfunction

	function void finish_test();
			check_data();
	endfunction
	
	covergroup cg_spi_received_data;
		coverpoint error_count{
			bins correct = {0};
			ignore_bins incorrect = {[1:$]};
		}
	endgroup
	
	covergroup cg_spi_crc_in_calculation;
		coverpoint error_count{
			bins correct = {0};
			ignore_bins incorrect = {[1:$]};
		}
	endgroup
	
	covergroup cg_spi_crc_out_calculation;
		coverpoint error_count{
			bins correct = {0};
			ignore_bins incorrect = {[1:$]};
		}
	endgroup
	
	covergroup cg_spi_crc_output;
		coverpoint error_count{
			bins correct = {0};
			ignore_bins incorrect = {[1:$]};
		}
	endgroup
	
	covergroup cg_spi_status_word_output;
		coverpoint error_count{
			bins correct = {0};
			ignore_bins incorrect = {[1:$]};
		}
	endgroup
	
	covergroup cg_spi_status_word_at_first;
		coverpoint error_count{
			bins correct = {0};
			ignore_bins incorrect = {[1:$]};
		}
	endgroup
	
	covergroup cg_spi_transmitted_data;
		coverpoint error_count{
			bins correct = {0};
			ignore_bins incorrect = {[1:$]};
		}
	endgroup
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		cg_spi_crc_in_calculation = new();
		cg_spi_crc_out_calculation = new();
		cg_spi_crc_output = new();
		cg_spi_received_data = new();
		cg_spi_status_word_at_first = new();
		cg_spi_status_word_output = new();
		cg_spi_transmitted_data = new();
	endfunction
	

endclass
