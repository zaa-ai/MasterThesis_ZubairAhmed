task do_mon();
	forever begin 
		@(vif.D); 
		void'(begin_tr(m_trans, "edge"));
		m_trans.value = vif.D;
		m_trans._val = m_trans.convert2enum(vif.D);
		end_tr(m_trans, $time());
		analysis_port.write(m_trans);
	end
endtask
