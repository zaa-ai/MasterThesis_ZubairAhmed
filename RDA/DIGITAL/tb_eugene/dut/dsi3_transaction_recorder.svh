/**
 * Class: dsi3_transaction_recorder
 * 
 * ...
 */
class dsi3_transaction_recorder extends uvm_component;
	
	`uvm_component_utils (dsi3_transaction_recorder)
	
	dsi3_master_tr master_transactions[1:0][$];
	dsi3_slave_tr slave_transactions[1:0][$];
	
	bit	enabled = 1'b0;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction

	virtual function void enable_recorder();
		enabled = 1'b1;
		clear_all();
	endfunction
	
	virtual function void disable_recorder();
		enabled = 1'b0;
	endfunction
	
	/**
	 * Received a DSI3 master transaction.
	 */
	// function void received_master_tr(int channel, dsi3_master_tr t);
	// 	if (enabled == 1'b1) begin
	// 		master_transactions[channel].push_back(t);
	// 	end
	// endfunction
		function void received_master_tr(int channel, dsi3_master_tr t);
		if (enabled == 1'b1) begin
		// ✅ Injected mistake: skip recording for channel 0 once
			static bit skip_once = 0;
			if (channel == 0 && !skip_once) begin
				skip_once = 1; // simulate missed transaction
				`uvm_info(this.get_name(), "Injected error: skipped logging master transaction for channel 0", UVM_LOW)
				return;
			end
			master_transactions[channel].push_back(t);
		end
	endfunction
	
	/**
	 * Received a DSI3 slave transaction.
	 */
	function void received_slave_tr(int channel, dsi3_slave_tr t);
		if (enabled == 1'b1) begin
			slave_transactions[channel].push_back(t);
		end
	endfunction
	
	function void clear_all();
		foreach(master_transactions[i]) begin
			master_transactions[i].delete();
		end
		foreach(slave_transactions[i]) begin
			slave_transactions[i].delete();
		end
	endfunction

	function dsi3_slave_tr get_slave_tr(int channel, int index);
		return slave_transactions[channel][index];
	endfunction
	
	function dsi3_slave_tr get_last_slave_tr(int channel);
		return slave_transactions[channel][$];
	endfunction
	
	function dsi3_master_tr get_master_tr(int channel, int index);
		return master_transactions[channel][index];
	endfunction
	
	function dsi3_master_tr get_last_master_tr(int channel);
		return master_transactions[channel][$];
	endfunction
	
	function int get_master_tr_count(int channel);
		return master_transactions[channel].size();
	endfunction
	
	function time get_master_tr_begin_time(int channel, int index);
		if(master_transactions[channel].size() == 0) return 0;
		return master_transactions[channel][index].get_begin_time();
	endfunction
	
	function time get_last_master_tr_begin_time(int channel);
		if(master_transactions[channel].size() == 0) return 0;
		return master_transactions[channel][$].get_begin_time();
	endfunction
	
	function void expect_tr_count_for_all_channels(int count);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			expect_tr_count(channel, count);
		end
	endfunction
	
	function void expect_tr_count(int channel, int count);
		if(enabled == 1'b0) begin
			`uvm_error(this.get_type_name(), $sformatf("expected master transactions count for channel %0d but transaction recorder is disabled!", channel))
			return;
		end
		if(master_transactions[channel].size() != count) begin
			`uvm_error(this.get_type_name(), $sformatf("Recorded unexpected number of master transactions at channel %0d, expected %0d, got %0d!", channel,  count, master_transactions[channel].size()))
			return;
		end
	endfunction
	
	function void expect_packets(int channel, dsi3_packet packets[$]);
		if(enabled == 1'b0) begin
			`uvm_error(this.get_type_name(), $sformatf("expected master transaction packets for channel %0d but transaction recorder is disabled!", channel))
			return;
		end
		// check number of recorded master transactions
		if(master_transactions[channel].size() != packets.size()) begin
			`uvm_error(this.get_type_name(), $sformatf("Recorded unexpected number of master transactions, expected %0d, got %0d!", packets.size(), master_transactions[channel].size()))
			return;
		end
		// check transmitted data 
		for(int i=0; i < packets.size(); i++) begin
			dsi3_master_tr next_tr = master_transactions[channel][i];
			dsi3_packet next_packet = packets[i];
			logic[3:0] half_byte_data[$];
			
			convert_queue#(1, 4)::convert(next_tr.data, half_byte_data, 1); // master transaction contains data as single bits
			
			if(half_byte_data.size() != next_packet.data.size()) begin
				`uvm_error(this.get_type_name(), $sformatf("Recorded unexpected number transmitted data, expected %0d symbols, got %0d!", next_packet.data.size(), half_byte_data.size()))
				return;
			end
			for(int k=0; k < next_packet.data.size(); k++) begin
				if(half_byte_data[k] != next_packet.data[k]) begin
					`uvm_error(this.get_type_name(), $sformatf("Recorded unexpected symbol data at index %0d, expected %1h, got %1h!", k, next_packet.data[k], half_byte_data[k]))
				end
			end
		end
	endfunction
	
	
endclass
