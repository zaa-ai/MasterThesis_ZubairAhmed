protected int bit_time_factor;
protected time last_edge;
bit discovery_mode;

task do_mon();
	forever begin	// From Master to Slave -> sensing voltage
		// reset values for new transmission
		discovery_mode = 1'b0;
		#1us;
		@(negedge vif.cable.Voltage);
		set_bit_time_factor();
		begin
			this.begin_tr(m_trans, this.get_name());
			m_trans.data.delete();
			
			fork
				mon_dm();
				mon_crm_pdcm();
			join
			
			m_trans.msg_type = dsi3_pkg::get_master_message_type_from_length(m_trans.data.size());

			this.end_tr(m_trans, last_edge);
		end
		if ((discovery_mode == 1'b1) || (m_trans.data.size() > 0)) begin
			`uvm_info({this.get_type_name(), " from ", this.get_parent().get_name()}, m_trans.convert2string(), UVM_HIGH)
			analysis_port.write(m_trans);
			m_trans = dsi3_master_tr::type_id::create("m_trans");
		end
	end
	`uvm_fatal ({this.get_type_name(), " from ", this.get_parent().get_name()}, "DSI3 Slave Monitor ended")
endtask

task mon_dm();
	fork
		begin	// timeout
			#(20us * bit_time_factor);
		end
		begin
			@(posedge vif.cable.Voltage);
			last_edge = $time;
			if (((last_edge - m_trans.get_begin_time()) > (15.84us * bit_time_factor)) && ((last_edge - m_trans.get_begin_time()) < (16.16us * bit_time_factor))) begin
				discovery_mode = 1'b1;
			end
		end
	join_any
	disable fork;					
endtask

task mon_crm_pdcm();
		begin
			automatic bit timeout_flag=1'b1;
			while(timeout_flag) begin //while (timeout_flag) begin
				#(7.8us*bit_time_factor);
				fork
					begin	// sampling the edge
						@(vif.cable.Voltage);
						last_edge = $time;
						m_trans.data.push_back(~vif.cable.Voltage);
						// skip if maximum (CRM) data is reached
						if(m_trans.data.size() == 32) begin
							timeout_flag = 1'b0;
						end
					end
					begin
						#(0.41us * bit_time_factor);	// edge should be in 7.92us ... 8.08us -> when not in time leave receiving
						timeout_flag = 1'b0;
					end
				join_any
				disable fork;
			end								
		end
endtask

function void set_bit_time_factor();
	dsi3_pkg::dsi3_bit_time_e bit_time = m_config.get_bit_time();
	bit_time_factor = dsi3_pkg::get_bit_time_factor(bit_time);
	m_trans.bit_time = bit_time;
endfunction
