task do_mon();
	if (m_config.is_active == UVM_PASSIVE) begin
		vif.full = 1'b1; // only when passive!
		vif.nearly_full = 1'b1; // only when passive!
	end
	fork 
		forever begin
			do begin
				@(posedge vif_clk_rst.clk or vif.action);
				#1ns;
			end while (vif.action == IDLE_WRITE);
			this.begin_tr(m_trans, get_name());
			action = vif.action;
			m_trans.action = action;
			case (action)
				BUFFER_WRITE, BUFFER_WRITE_FIRST: begin
					if (m_config.is_active == UVM_ACTIVE) begin
						do_buffer_write();
					end
					else begin
						@(negedge vif_clk_rst.clk);
						m_trans.data = vif.data.data;
						m_trans.ecc = vif.data.ecc;
						do_ready();
					end
				end
				BUFFER_INVALIDATE, BUFFER_VALIDATE, BUFFER_CLEAR: begin
					do_ready();
				end
			endcase
			write_transaction();
		end
		forever begin  // only when passive!
			@(posedge vif_clk_rst.clk);
			if ((m_config.is_active == UVM_PASSIVE) && (m_config.is_completly_passive == 1'b0))
				vif.ready = 1'b0;
		end
	join_any
	`uvm_fatal(this.get_type_name(), "Buffer writer monitor stopped monitoring!!!");
endtask
	
task do_ready();
	if (m_config.is_completly_passive) begin
		if(m_config.vif.ready != 1'b1)
			@(posedge m_config.vif.ready);
	end
	else begin
		#10ns;
		vif.ready = 1'b1;   // only when passive!
	end
endtask
	
task do_buffer_write();
	if (vif.ready != 1'b1)
		@(posedge vif.ready);
	m_trans.data=vif.data.data;
	m_trans.ecc =vif.data.ecc;
endtask
	
function void write_transaction();
	this.end_tr(m_trans);
	`uvm_info(this.get_type_name(), m_trans.convert2string(), UVM_DEBUG)
	analysis_port.write(m_trans);
	m_trans = buffer_writer_tr::type_id::create("m_trans");
endfunction
