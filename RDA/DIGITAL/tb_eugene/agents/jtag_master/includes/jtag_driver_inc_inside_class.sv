// variables set with values from config DB
logic[265:0]	jtag_read_data;			// JTAG data shifted out

typedef enum {JTAG_IR=0, JTAG_DR=1} JTAG_REG_SEL;

task run_phase(uvm_phase phase);
	
	end_jtag_req();
	enable_jtag();
	
	forever
	begin
		seq_item_port.get_next_item(req);
		
		start_jtag_req(req.init_jtag);

		// instruction to be sent ?
		if(req.ir_length != 0) begin
			jtag_send(JTAG_IR, req); 
			req.read_ir = jtag_read_data;
		end
		// data to be sent?
		if(req.dr_length != 0) begin
			jtag_send(JTAG_DR, req);
			req.read_dr = switch_bit_order(jtag_read_data, req.dr_length);
		end
		end_jtag_req();					
			
		`uvm_info("JTAG", req.convert2string(), UVM_HIGH);

		// The driver sends an explicit response transaction back to the sequence
		seq_item_port.item_done(rsp);
	end
endtask : run_phase


task jtag_send(int register_selector, jtag_tr req);
	logic[265:0] value  = register_selector == JTAG_DR ? req.dr_value  : req.ir_value;
	int         length  = register_selector == JTAG_DR ? req.dr_length : req.ir_length;
		 
	// ##	goto sel_dr 
	jtag_clock(1, 0);
	if(register_selector==JTAG_IR) begin 
		// ##	goto sel_ir 
		jtag_clock(1, 0);
	end	else begin
	end
	// ##	goto cap_ir / cap_dr
	jtag_clock(0, 0);

	jtag_read_data = 0;
	// ##	goto shift_ir / shift_dr
	jtag_clock(0, 0);
		
	// ## shift data into IR
	repeat(length - 1) begin
		jtag_clock_data(0, value & 1 ? 1 : 0, register_selector, req);
		value = value >> 1;
	end
	// ## goto exit_ir and shift in last data
	jtag_clock_data(1, value & 1 ? 1 : 0, register_selector, req);
		
	// ##	goto upd_ir / upd_dr
	jtag_clock(1, 0);
		
	// ## goto run_idle
	jtag_clock(0, 0);
				
endtask : jtag_send

task jtag_init();
	repeat(5) begin
		jtag_clock(1, 1);
	end
	// ##	exit reset state --> goto run_idle
	jtag_clock(0, 1);
endtask : jtag_init

task jtag_go_run_idle();
	jtag_clock(0, 0);
endtask : jtag_go_run_idle

task start_jtag_req(bit init);
	vif.TCK = !m_config.leading_level;
	vif.TRST = 1'b1;
	// do JTAG init on demand
	if(init) begin
		jtag_init();
	end
endtask : start_jtag_req

task end_jtag_req();
	vif.TMS = 1'b0;
	vif.TDI = 1'b0;
	vif.TCK = !m_config.leading_level;
	
endtask : end_jtag_req

task disable_jtag();
	vif.TRST = 1'b0;
endtask : disable_jtag
	
task enable_jtag();
	vif.TRST = 1'b1;
endtask : enable_jtag

/*
 * tms : TMS level
 * init: wird jtag init durchgeführt oder nicht?
 */
task jtag_clock(logic tms, logic init);
	vif.TMS = tms;
	#(m_config.cycle_time/2);
	vif.TCK = m_config.leading_level;
	#(m_config.cycle_time/2);
	vif.TCK = !m_config.leading_level;
endtask : jtag_clock


task jtag_clock_data(logic tms, logic tdi, int register_selector, jtag_tr req);
	#(m_config.cycle_time/4);
	vif.TDI = tdi;
	vif.TMS = tms;
	jtag_read_data = jtag_read_data * 2 + (vif.TDO === 1'b1 ? 1 : 0);
	#(m_config.cycle_time/4);
	vif.TCK = m_config.leading_level;
	#(m_config.cycle_time/4);
	#(m_config.cycle_time/4);
	vif.TCK = !m_config.leading_level;
	// for debug
	uvm_report_info(get_type_name(), 
			$sformatf("\nTime: %d us: read bit %d (data=%d)", $time() / 1us, vif.TDO, jtag_read_data), UVM_DEBUG);
endtask : jtag_clock_data



function logic [265:0] switch_bit_order(logic [265:0] value, int length);
	automatic logic [265:0] tmp_val = '0;
	
	repeat(length) begin
		tmp_val = tmp_val << 1;
		if (value & 1)
			tmp_val = tmp_val+266'd1;
		value = value >> 1;
	end
	return tmp_val;
	
endfunction : switch_bit_order
