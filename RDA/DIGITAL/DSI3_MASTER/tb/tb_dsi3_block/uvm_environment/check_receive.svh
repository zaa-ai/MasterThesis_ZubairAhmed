/**
 * Class: check_transmit
 * 
 * Checker for data written into buffer received from the DSI3 slave
 */
virtual class check_receive #(type T) extends uvm_scoreboard;
	
	uvm_analysis_imp_dsi3_master	#(dsi3_master_tr,	check_receive#(T))  dsi3_master_export;
	uvm_analysis_imp_dsi3_slave		#(dsi3_slave_tr,	check_receive#(T))  dsi3_slave_export;
	uvm_analysis_imp_buffer_writer	#(T,	            check_receive#(T))  buffer_writer_export;
	
	//TODO: check period
	//TODO: check WAIT
	
	localparam	time	transceiver_delay = 3us;
	
	
	protected	int error_count;
	time		master_start_time;
	bit 		receiving;
	
	protected	dsi3_slave_tr		transmissions[$];
	protected	T	buffer_writes[$];
	protected	T	buffer_slave_transmission[$];
	protected	dsi3_pkg::dsi3_msg_type msg_type;
	protected	dsi3_master_configuration_tr	configuration;
	protected	int	number_of_received_packets;
                int defined_slave_answer;

	
	function new (string name = "check_receive", uvm_component parent=null);
		super.new(name, parent);
		buffer_writer_export = new("writer_export", this);
		dsi3_slave_export = new("dsi3_slave_export", this);
		dsi3_master_export = new("dsi3_master_export", this);
		receiving = 1'b0;
        defined_slave_answer = 0;
	endfunction
	
    virtual function void clear_transmissions();
        transmissions.delete();
    endfunction
    
    virtual function void initialize();
        transmissions.delete();
        buffer_writes.delete();
        buffer_slave_transmission.delete();
        error_count = 0;
        receiving = 1'b0;
        defined_slave_answer = 0;
        number_of_received_packets = 0;
    endfunction
    
	virtual task start_checking();
		#20us;
		compare_buffer_queues();
		void'(transmissions.pop_front());
	endtask
	
	virtual function void write_buffer_writer(T t); // second
		`uvm_info(this.get_type_name(), $sformatf("%s Buffer :%s", msg_type.name, t.convert2string()), UVM_HIGH)
		buffer_writes.push_back(t);
    endfunction
    
	virtual function void write_dsi3_master(dsi3_master_tr t);
		if (msg_type == t.msg_type) begin
			this.master_start_time = t.get_begin_time();
			if (defined_slave_answer == 0) this.number_of_received_packets = 0;
			receiving = 1'b1;
		end
		else receiving = 1'b0;
	endfunction
	
	virtual function void write_dsi3_slave(dsi3_slave_tr t); // first
		if (receiving == 1'b1) begin
			process_dsi3_slave_response(t);
		end
		else begin
			`uvm_info(this.get_type_name(), $sformatf("DSI3 slave not saved:%s", t.convert2string()), UVM_HIGH)
		end
	endfunction
	
	virtual function void process_dsi3_slave_response(dsi3_slave_tr t);
        if (defined_slave_answer == 0) add_dsi3_slave_response(t);
        else number_of_received_packets++;
		`uvm_info(this.get_type_name(), $sformatf("DSI3 slave:%s", t.convert2string()), UVM_HIGH)
		fork
			start_checking();
		join_none
    endfunction
    
    virtual function void add_dsi3_slave_response(dsi3_slave_tr t);
		number_of_received_packets++;
		transmissions.push_back(t);
		fill_buffer_queue(t);
    endfunction
    
    virtual function void set_slave_response(dsi3_slave_tr t);
        defined_slave_answer = 1;
        add_dsi3_slave_response(t);
        number_of_received_packets--;
    endfunction
    
    pure virtual function void fill_buffer_queue(dsi3_slave_tr t, int packet_index = 0);
	
	protected virtual function void check_data();
		if (transmissions.size() > 0) begin
			`uvm_error(this.get_type_name(), $sformatf("not all %s tranmissions written to buffer. %1d remaining", msg_type.name, transmissions.size()))
			foreach (transmissions[i]) begin
				`uvm_info(this.get_type_name(), $sformatf("%s",transmissions[i].convert2string()), UVM_HIGH)
			end
			error_count++;
		end
		if (number_of_received_packets == 0) begin
			if (msg_type == CRM) begin
				compare_buffer_queues();
			end
		end
	endfunction
	
	virtual function int get_error_count();
		check_data();
		return error_count;
	endfunction
	
	
	virtual function void zero_data_not_in_symbol_count(int symbol_count, ref logic[15:0]	data[$]);
		int symbol_index;
		int word_index=0, nibble_index=0;
		for (symbol_index = 0; symbol_index< (data.size()*4); symbol_index++) begin
			if (symbol_index >= symbol_count) begin
				data[word_index][15-(nibble_index*4)-:4] = '0;
			end
			if (nibble_index == 3) begin
				nibble_index = 0;
				word_index++;
			end
			else					nibble_index++;
		end
	endfunction
	
	virtual function void add_empty_packet_when_no_response_received_in_crm();
		
	endfunction
	
    pure virtual function void compare_buffer_queues();
    
    virtual function void set_configuration(dsi3_master_configuration_tr    t);
        this.configuration = t;
    endfunction
    
    
endclass
