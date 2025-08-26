task do_mon();
	fork 
		forever begin
			m_trans = buffer_reader_tr::type_id::create("buffer_reader_tr");
			do begin
				@(posedge vif_clk_rst.clk or vif.action);
				#1ns;
			end	while( vif.action == IDLE_READ);
			action = vif.action;
			this.begin_tr(m_trans, get_name());
			m_trans.action = action;
			case (action)
				BUFFER_READ: begin
					do_ready();
					#1ns;
					m_trans.data = vif.data.data;
					m_trans.ecc  = vif.data.ecc;
				end
				BUFFER_MOVE_POINTER: begin
					do_ready();
					#1ns;
					m_trans.data = vif.step;
				end
			endcase
			this.end_tr(m_trans);
			`uvm_info(this.get_type_name(), m_trans.convert2string(), UVM_DEBUG)
			analysis_port.write(m_trans);
		end
	join_any
	`uvm_fatal(this.get_type_name(), "Buffer reader monitor stopped monitoring!!!");
endtask


task do_ready();
	if (vif.ready != 1'b1) begin
		do begin
			@(negedge vif_clk_rst.clk); #1ns;
		end while( vif.ready == 1'b0);
	end
endtask
