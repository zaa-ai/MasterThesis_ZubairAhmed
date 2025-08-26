/**
 * Class: spi_dsi_wait_seq
 * 
 * Sets a DSI transmission wait time
 */
class spi_dsi_wait_seq extends spi_dsi_command_seq;
	
	rand logic msb_filler;
	rand logic[14:0] wait_time;
	
	`uvm_object_utils_begin(spi_dsi_wait_seq)
		`uvm_field_int(wait_time, UVM_DEFAULT | UVM_UNSIGNED | UVM_DEC )
	`uvm_object_utils_end
	
	covergroup cov_dsi_wait;
		option.per_instance = 0;
		coverpoint channel_bits;
		coverpoint wait_time {
			bins min = {0};
			bins very_short = {15'h1, 15'hF};
			bins short = {  15'h10, 15'hFF};
			bins med   = { 15'h100, 15'h3FFE};
			bins long  = {15'h3FFF, 15'h7FFE};
			bins max   = {15'h7FFF};
		}
		cross wait_time, channel_bits;
	endgroup
	
	/************************ Methods declarations ************************/
	function new(string name = "DSI wait");
		super.new(name);
		cov_dsi_wait = new();
	endfunction
	
	virtual function void sample_cov();
		super.sample_cov();
		cov_dsi_wait.sample();
	endfunction
	
	virtual function spi_cmd_type get_command_code();
		return CMD_DSI_WAIT;
	endfunction
		
	virtual function int get_word_count();
		return 2;
	endfunction	
	
	virtual function logic[15:0] get_word(int index);
		if(index == 1) begin
			return {msb_filler, wait_time};
		end
		return super.get_word(index);
	endfunction
	
	virtual function bit create_from(logic[15:0] data_in[$], logic[15:0] data_out[$]);
		if(data_in.size() < get_word_count()) begin
			return 0;
		end
		msb_filler = data_in[1][15];
		wait_time  = data_in[1][14:0];
		return super.create_from(data_in, data_out);
	endfunction
	
	virtual function string convert2string();
		return $sformatf("DSI wait for %0d us at channels %04b", wait_time, channel_bits);
	endfunction
	
endclass