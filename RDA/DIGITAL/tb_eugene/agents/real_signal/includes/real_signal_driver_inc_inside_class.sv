task run_phase(uvm_phase phase);

	vif.PIN <= m_config.init_value;
	
	forever
	begin
		real start_value;
		real end_value;
		time start_time;
		time duration;
		time edge_duration;
		
		seq_item_port.get_next_item(req);
		
		start_time		= $time;
		duration		= req.duration * m_config.time_scale;
		edge_duration	= req.edge_duration * m_config.time_scale;
		start_value		= vif.PIN;
		end_value		= req.value * m_config.value_scale;
	  
		while ($time - start_time < edge_duration) begin
			real current_value = start_value + (end_value - start_value) * ($time - start_time) / edge_duration;
			vif.PIN <= current_value;
			#1ns;
		end
		
		vif.PIN <= end_value;
		if (duration > edge_duration) begin
			#(duration-edge_duration);
		end

		// The driver sends an explicit response transaction back to the sequence
		seq_item_port.item_done(rsp);
	end
endtask : run_phase