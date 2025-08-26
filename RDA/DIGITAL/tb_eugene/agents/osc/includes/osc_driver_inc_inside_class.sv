int		freq;
bit		enabled;
//event to know when the clock is disabled
uvm_event disabled_clock;
uvm_event_pool local_pool;

task run_phase(uvm_phase phase);
	`uvm_info(get_type_name(), "run_phase", UVM_HIGH)
	// initialize if
	osc_init();
	fork
		receive_req();
		drive_clk();
	join
endtask : run_phase
/*
	| #	| Software	| Hardware	|	Action
	|	|	EN		|	EN		|
	|-----------------------------------------------------------------
	| 1	|	0		|	0/1		| wait for software enable
	|	|			|			| --> wait for next transaction item
	|	|			|			| --> no clocking
	|-----------------------------------------------------------------
	| 2	|	1		|	0		| wait for hardware enable OR reconfiguration
	|	|			|			| --> wait for next transaction item OR
	|	|			|			| --> change of EN in interface
	|	|			|			| --> no clocking
	|-----------------------------------------------------------------
	| 3	|	1		|	1		| clocking AND
	|	|			|			| (checking hardware enable OR reconfiguration)
	|	|			|			| --> wait for next transaction item OR
	|	|			|			| --> change of EN in interface
	|	|			|			| --> clocking (half of period unless diabled via hardware enable)
	|-----------------------------------------------------------------
 */

task drive_clk();
	forever begin // clocking
		if ((enabled == 1) && (vif.EN == 1)) begin
			vif.CLK = ~vif.CLK;
			#(1.0s/(2*freq));
		end
		else begin // wait
			@(posedge enabled or posedge vif.EN);
		end
	end	
endtask : drive_clk

task receive_req();
	local_pool = uvm_event_pool::get_global_pool();
	forever begin
		seq_item_port.get_next_item(req);
		`uvm_info(get_type_name(), {"req item\n",req.sprint}, UVM_DEBUG)
		freq = req.freq;
		enabled = req.enabled;
		if (req.enabled == 0)
			begin
				disabled_clock = local_pool.get("disabled_clock");
				disabled_clock.trigger();
			end
			
		seq_item_port.item_done(rsp);
	end	
endtask : receive_req

task osc_init();
	vif.CLK	= 1'b0;
	freq = m_config.initial_frequency;
	enabled = m_config.initial_enabled;
endtask : osc_init
