protected bit			end_flag;

task wait_for_sampling();
	bit 	flag = 1'b0;
	time	delay;
	fork
			begin		// try to detect edge
				@(vif.cable.Current);
				flag = 1'b1;
			end
			begin		// wait for possible edge
				time delay = 0.85us*m_config.get_chip_time();		// ( chip time / 2.0 ) + (0.35 * chip time )
				#(delay);
			end
		join_any
	disable fork;
	
	if (flag) begin		// if edge occurred -> wait half a chip
		delay = (1.0us * m_config.get_chip_time()) / 2.0;
		#(delay);
	end
	else	begin	// if no edge occured -> wait for exactly 1 chip 
		delay = (0.15us * m_config.get_chip_time());				// ( chip time / 2.0 ) - (0.35 * chip time )
		#(delay);
	end
endtask : wait_for_sampling

task do_mon();
	
	forever begin	// From Slave to Master -> sensing current
		dsi3_pkg::dsi3_symbol symbol = {dsi3_pkg::CX, dsi3_pkg::CX, dsi3_pkg::CX};
		@(vif.cable.Current);
		end_flag = 0;
		if (vif.cable.Current > 0) begin
			this.begin_tr(m_trans, get_name());
			m_trans.symbol_coding_error = 1'b0;
			m_trans.symbol_coding_error_injection = NOT_SET;
			m_trans.chip_length_error_injection = NOT_SET;
			m_trans.data.delete();
			#(0.5us * m_config.get_chip_time());		// wait for first time to sample
			while (!end_flag) begin
				for (int j=2; j>=0; j--) begin
					if ((vif.cable.Current == int'(dsi3_pkg::C0)) && (j==2)) begin	// if first chip in symbol is 0 
						j=0;									// end loop
						end_flag = 1;							// end transmission
					end
					else begin
						symbol[j] = dsi3_pkg::dsi3_chip'(vif.cable.Current);		// sample value
						wait_for_sampling();
					end
				end
				if (!end_flag) begin							// if the end is not indicated
					logic[3:0]	symbol_decoded;
					symbol_decoded = dsi3_pkg::get_symbol(symbol);
					m_trans.data.push_back(symbol_decoded);
					if ($isunknown(symbol_decoded)) begin
						m_trans.symbol_coding_error |= 1'b1;
					end
				end
			end
			this.end_tr(m_trans);
			`uvm_info({this.get_type_name(), " from ", this.get_parent().get_name()}, m_trans.convert2string(), UVM_HIGH)
			analysis_port.write(m_trans);
			m_trans = dsi3_slave_tr::type_id::create("m_trans");
		end
	end
	
	`uvm_fatal (this.get_type_name(), "DSI3 Slave Monitor ended")
	
endtask
