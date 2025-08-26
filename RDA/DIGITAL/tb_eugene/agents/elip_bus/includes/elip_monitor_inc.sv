task do_mon();
	forever begin
		@(negedge vif.clk iff ((vif.read | vif.write == 1'b1) && (vif.rstn == 1'b1)));
		this.begin_tr(m_trans, get_name());

		m_trans.data_write = vif.data_write;
		m_trans.data_write_ecc = vif.data_write_ecc;
		m_trans.address = vif.address;

		if (vif.write == 1'b1) begin
			m_trans.write = 1'b1;
		end
		else begin
			m_trans.write = 1'b0;
		end
		@(posedge vif.ready);
		m_trans.data_read = vif.data_read;
		m_trans.data_read_ecc = vif.data_read_ecc;
		this.end_tr(m_trans);
		`uvm_info(this.get_type_name(), m_trans.convert2string(), UVM_DEBUG)
		analysis_port.write(m_trans);
	end
endtask
