// variables set with values from config DB
protected timing_iterator slave_timing_iterator;
protected int value;

task run_phase(uvm_phase phase);
	vif.cable.Current = 0; // initialize DSI3 interface
	forever	begin
		seq_item_port.get_next_item(req);
		do_drive();
		seq_item_port.item_done(rsp);
	end
endtask : run_phase

task do_drive ();
	if (req.msg_type == dsi3_pkg::DM) begin
		do_dm();
	end
	else begin
		do_crm_pdcm();
	end
endtask


task do_dm(); 
	if(slave_timing_iterator.has_next()) begin
		slave_rxd_timing rxd_timing = slave_timing_iterator.next();
		real tolerance = req.tolerance;
		fork
			#(32us * tolerance);
			ramptovalue_dm(2, (27us * tolerance));
		join
		ramptovalue(0, rxd_timing);													// finish data transfer		
	end
	else begin
		`uvm_error(this.get_name(), "No Timing available for this packet")
	end
endtask

task ramptovalue_dm (int value, time ramp_time = 1us);
	if (value != vif.cable.Current) begin
		int	direction = value - vif.cable.Current;				// direction > 0 => posedge
		int	abs = (direction > 0) ? (direction) : -direction;
		direction /= abs;
		while (value != vif.cable.Current) begin
			#(ramp_time / (1+abs));
			vif.cable.Current += direction;
		end
		fork
			inject_error();
			#(ramp_time / (1 + abs));
		join
	end
	else begin
		#1us;
	end
endtask

task do_crm_pdcm();
	dsi3_pkg::dsi3_symbol	symbol;
	array_of_ints error_bits = get_error_flag_for_symbol(req.symbol_coding_error_injection, req.data.size());
	
	bit chip_length_error = (req.chip_length_error_injection == ALWAYS_ERROR || req.chip_length_error_injection == RANDOM_ERROR) ? 1'b1 : 1'b0;
	int chip_length_error_index = $urandom_range(0, req.data.size()-1); 
	
	if(slave_timing_iterator.has_next()) begin
		slave_rxd_timing rxd_timing = slave_timing_iterator.next();
		for (int i=0; i<req.data.size() ; i++) begin
			symbol = get_symbol(req.data[i], error_bits[i][0]);
			req.symbol_coding_error |= error_bits[i][0];
			if(chip_length_error == 1'b1 && chip_length_error_index == i) begin
				send_symbol(symbol, rxd_timing, 1'b1);
				chip_length_error = 1'b0;
			end 
			else begin
				send_symbol(symbol, rxd_timing, 1'b0);
			end
		end
		ramptovalue(0, rxd_timing);									// finish data transfer
	end
	else begin
		`uvm_error(this.get_name(), "No Timing available for this packet")
	end
	
endtask

function dsi3_pkg::dsi3_symbol get_symbol(logic[3:0] data, bit symbol_error);
	dsi3_pkg::dsi3_symbol	symbol;
	if (symbol_error) begin
		//TODO: add errors with 0 at start
		symbol = get_erroneous_symbol();
	end
	else begin
		symbol = get_symbol_from_data(data);
	end	
	return symbol;
endfunction

function dsi3_pkg::dsi3_symbol get_symbol_from_data(logic[3:0] data);
	dsi3_pkg::dsi3_symbol symbol;
	symbol = dsi3_pkg::dsi3_symbol_lut[data];
	return symbol;
endfunction

function array_of_ints get_error_flag_for_symbol(error_injection_e error_injection, int size);
	array_of_ints errors_in_symbols;
	case (error_injection)
		ALWAYS_ERROR : begin
			errors_in_symbols = get_errors(size);
		end
		RANDOM_ERROR: begin
			randcase
				1: begin
					errors_in_symbols = get_errors(size);
				end
				7: begin
					errors_in_symbols = get_empty_array(size);
				end
			endcase			
		end
		default: begin
			errors_in_symbols = get_empty_array(size);
		end
	endcase
	return errors_in_symbols;
endfunction

function array_of_ints get_empty_array(int size);
	get_empty_array = new[size];
endfunction

function array_of_ints get_errors(int size);
	array_of_ints errors_in_symbols;
	std::randomize(errors_in_symbols) with {
			errors_in_symbols.size() == size;
			foreach(errors_in_symbols[i]) {
				errors_in_symbols[i] dist {0:= 8, 1:=1};
			}
			errors_in_symbols.sum > 0;
		};
	return errors_in_symbols;
endfunction

function dsi3_pkg::dsi3_symbol get_erroneous_symbol();
	dsi3_pkg::dsi3_symbol error_symbol;
	randcase
		1: error_symbol = dsi3_pkg::dsi3_symbol'({dsi3_pkg::C1, dsi3_pkg::C1, dsi3_pkg::C1});
		1: error_symbol = dsi3_pkg::dsi3_symbol'({dsi3_pkg::C2, dsi3_pkg::C2, dsi3_pkg::C2});
	endcase	
	return error_symbol;
endfunction


task send_symbol(dsi3_pkg::dsi3_symbol symbol, slave_rxd_timing rxd_timing, bit chip_length_error);
	real tolerance = req.tolerance;
	time delay = (req.chiptime * 1.0us * tolerance);
	int chip_length_error_index;
	if (chip_length_error == 1'b1) chip_length_error_index = $urandom_range(2,0);
	for (int chip_index =(req.chips_per_symbol-1); chip_index>=0; chip_index--) begin
		bit do_error = 1'b0;
		value = symbol[chip_index];
		if(chip_length_error == 1'b1 && chip_index == chip_length_error_index) begin
			do_error = 1'b1;
		end
		fork
			ramptovalue(value, rxd_timing);
			begin
				#(delay);
				if (do_error == 1'b1) #1us;
			end
		join
	end	
endtask

/*
 * Task: dsi3_slave_driver::ramptovalue
 * 
 * Ramps the current value of the DSI to the value given as parameter from the current value in 1us
 * 
 * Parameters:
 * - int value 
 */
task ramptovalue (input int value, input slave_rxd_timing rxd_timing);
	int current_value = vif.cable.Current;
	if (current_value != value) begin
		time delay_rxd1 = rxd_timing.t_rxd1[current_value][value];
		time delay_rxd2 = rxd_timing.t_rxd2[current_value][value];
		int	direction = value - current_value;				// direction > 0 => posedge
		int	abs = (direction > 0) ? (direction) : -direction;
		direction /= abs;
		
		fork
			begin
				if (delay_rxd1 != 0) begin
					#delay_rxd1;
					vif.cable.Current += direction;				
				end
			end
			begin
				if (delay_rxd2 != 0) begin
					#delay_rxd2;
					vif.cable.Current += direction;
				end
			end
			inject_error();
		join
	end
endtask 

task inject_error();
	if(m_config.chip_time_error > 0.0) begin
		int current_value;
		time error_duration = req.chiptime * 1us * m_config.chip_time_error;
		int max_delay = int'(1000 * req.chiptime * (1.0 - m_config.chip_time_error));
		time delay = $urandom_range(1000, max_delay) * 1ns; 
		#(delay);
		current_value = vif.cable.Current;
		randcase
			1 : vif.cable.Current = 0;
			1 : vif.cable.Current = 1;
			1 : vif.cable.Current = 2;
		endcase
		#(error_duration);
		vif.cable.Current = current_value;
	end
	else begin
		#1ns;
	end
endtask : inject_error

function void set_iterator(timing_iterator iterator);
	slave_timing_iterator = iterator;
endfunction

function timing_iterator get_timing_iterator();
	return slave_timing_iterator;
endfunction