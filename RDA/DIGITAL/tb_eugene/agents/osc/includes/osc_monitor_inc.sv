
`define DEFAULT_FREQ 500000

task do_mon();	
	time old_clk_edge 	= '0;	
	real old_freq 		= 0.0;
	real freq 			= 0.0;
	bit clkref_ok		= 1'b0;
	bit old_en			= 1'b0;
	
	fork
		begin
			forever begin
				@(vif.EN) begin

//					`uvm_info(get_type_name(), $sformatf("OSC EN = %b %t", vif.EN, $time), UVM_HIGH)
					
					m_trans.enabled = vif.EN;		
					old_en = vif.EN;					
					analysis_port.write(m_trans);
				end
			end
		end
		begin
			forever begin
				@(posedge vif.CLK)
				freq 			= ($time - old_clk_edge) / 1.0s;
				if (freq > 0)
					freq = 1.0 / freq;			
							
				if (clkref_ok) begin
//					if ($abs(freq - `DEFAULT_FREQ) > 1000.0) begin 
					if ($abs(freq - `DEFAULT_FREQ) > 5100.0) begin 
						m_trans.freq 	= freq;
						m_trans.enabled = vif.EN;
						analysis_port.write(m_trans); 
						
//						`uvm_info(get_type_name(), $sformatf("OSC FREQ WRONG %h %t", freq, $time), UVM_HIGH)
						clkref_ok 		= 1'b0;	
					end					
				end
				else begin
//					if ($abs(freq - `DEFAULT_FREQ) <= 1000.0) begin 
					if ($abs(freq - `DEFAULT_FREQ) <= 5100.0) begin 
						m_trans.freq 	= freq;
						m_trans.enabled = vif.EN;
						analysis_port.write(m_trans); 
						
//						`uvm_info(get_type_name(), $sformatf("OSC FREQ GOOD %h %t", freq, $time), UVM_HIGH)
						clkref_ok 		= 1'b1;	
					end							
				end
				old_clk_edge 	= $time;
				old_freq = freq;
			end
		end
	join_any
	
endtask
