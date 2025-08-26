typedef class dsi3_slave_seq;
typedef class dsi3_slave_tr_container_seq;
/**
 * Class: dsi3_master_subscriber
 * 
 * Subscribes to messages from the DSI3 master monitor of type <dsi3_master_tr> to create sequences for the slave driver
 */
class dsi3_master_subscriber extends uvm_subscriber #(dsi3_master_tr);
	
	`uvm_component_utils(dsi3_master_subscriber)
	
	dsi3_slave_pkg::dsi3_slave_config			m_config;
	dsi3_slave_sequencer_t						m_sequencer;
	protected dsi3_slave_tr						m_slave_tr;
	protected dsi3_master_pkg::dsi3_master_tr	m_master_tr;
	protected event								new_master_transaction;
	protected int								dm_pulse_cnt=0;
	
	uvm_tlm_analysis_fifo #(tdma_scheme) crm_tdma_fifo;
	uvm_tlm_analysis_fifo #(tdma_scheme) pdcm_tdma_fifo;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		m_slave_tr = dsi3_slave_tr::type_id::create("dsi3_slave_tr", this);
		crm_tdma_fifo = new("crm_tdma_fifo", this);
		pdcm_tdma_fifo = new("pdcm_tdma_fifo", this);
	endfunction	
	
	/*	
	 * Function: write
	 * 
	 * This function is called by the monitor of the DSI3 master agent to transmit the received message.
	 * It triggers the event 'new_master_transaction' and starts a slave transaction on the corresponding sequencer.
	 * 
	 * Parameters:
	 * - dsi3_master_tr t  - received message from the DSI3 master
	 */
	function void write(dsi3_master_tr t);
		m_master_tr = new();
		m_master_tr.copy(t);
		m_master_tr.record();
		-> new_master_transaction;
	endfunction
	
	task run_phase(uvm_phase phase);
		forever begin
			@new_master_transaction;
			send_slave_response(m_master_tr);
		end
	endtask
	
	/*	
	 * Task: send_slave_response
	 * 
	 * Task description needed
	 * 
	 * Parameters:
	 * - dsi3_master_tr m_master_tr 
	 */
	task send_slave_response(dsi3_master_tr m_master_tr);
		case (m_master_tr.msg_type)
			dsi3_pkg::PDCM	: do_pdcm(m_master_tr);
			dsi3_pkg::CRM	: do_crm(m_master_tr);
			dsi3_pkg::DM	: do_dm(m_master_tr);
			default: begin
				if(checker_config::get().enable_error_if_unknown_transaction_size) `uvm_error(this.get_name(), $sformatf("DSI3 master transaction size is not supported: %d", m_master_tr.data.size()))
			end
		endcase
	endtask
	
	/*###   DM   ######################################################*/
	task do_dm(dsi3_master_tr master_tr);
		time 	delay;
		tdma_scheme scheme = m_config.dm_scheme;
		int	enabled_slaves = scheme.get_packet_count();
		
		if (dm_pulse_cnt < enabled_slaves) begin 
			// get slave number
			tdma_scheme_packet packet = scheme.packets[dm_pulse_cnt];
			if (packet.enable == 1'b1) begin
				time delay_time;
				
				if(packet.randomize(start_time, tolerance_int) != 1) `uvm_error(this.get_name(), "randomization failed");
				delay_time = packet.start_time * dsi3_pkg::get_bit_time_factor(master_tr.bit_time);
				
				delay = get_delay(m_master_tr, delay_time);
				if(delay != -64'd1) begin
					dsi3_slave_tr_container_seq seq = new("dm_response");
					#(delay);
					if(m_slave_tr.randomize with {msg_type == dsi3_pkg::DM; tolerance_int == local::packet.tolerance_int; data.size() == 1;} != 1) `uvm_error(this.get_name(), "randomization failed");
					seq.req = m_slave_tr;
					seq.start(m_sequencer);
				end
			end
			dm_pulse_cnt++;
		end
		else begin
			dm_pulse_cnt = 0;
		end
	endtask
	
	/*###   PDCM   ######################################################*/
	task do_pdcm(dsi3_master_tr m_master_tr);
		dm_pulse_cnt = 0;
		send_packet_from_tdma_scheme(m_master_tr, get_scheme(pdcm_tdma_fifo, m_config.get_pdcm_scheme()));
	endtask
	
	/*###   CRM   ######################################################*/
	task do_crm(dsi3_master_tr m_master_tr);
		dm_pulse_cnt = 0;
		send_packet_from_tdma_scheme(m_master_tr, get_scheme(crm_tdma_fifo, m_config.get_crm_scheme()));
	endtask
	
	function tdma_scheme get_scheme(uvm_tlm_analysis_fifo #(tdma_scheme) fifo, tdma_scheme default_scheme);
		tdma_scheme scheme;
		if(fifo.can_get()) begin
			// just take scheme from FIFO if there is one
			void'(fifo.try_get(scheme));
		end
		else begin
			// use default scheme, randomize it before usage
			foreach(default_scheme.packets[i]) begin
				tdma_scheme_packet tdma_packet = default_scheme.packets[i]; 
				if ((tdma_packet.symbol_count > 0) && (tdma_packet.enable)) begin 
					if(tdma_packet.randomize(start_time, tolerance_int) != 1) `uvm_error(this.get_name(), "randomization failed");
					if(tdma_packet.packet.randomize(data, crc_correct) with {
							(tdma_packet.crc_error_injection == NEVER_ERROR || tdma_packet.crc_error_injection == ALWAYS_ERROR) -> crc_correct == 1'(tdma_packet.crc_error_injection);
							data.size() == tdma_packet.symbol_count;}
							!= 1) `uvm_error(this.get_name(), "randomization failed");
				end
			end
			scheme = default_scheme;
		end
		return scheme;
	endfunction
	
	task send_packet_from_tdma_scheme(dsi3_master_tr m_master_tr, tdma_scheme scheme);
		foreach(scheme.packets[i]) begin
			tdma_scheme_packet tdma_packet = scheme.packets[i];
			// send only when symbol_count > 0 -> otherwise no data to send
			if ((tdma_packet.symbol_count > 0) && (tdma_packet.enable)) begin 
				fork
					send_delayed(tdma_packet, m_master_tr, scheme.chiptime);
				join_none;
			end
		end
	endtask
		
	task send_delayed(tdma_scheme_packet tdma_packet, dsi3_master_tr m_master_tr, int chiptime);
		time delay = get_delay(m_master_tr, tdma_packet.get_start_time()); // calculate delay from start of pulse to current start time
		if(delay != -64'd1) begin
			#(delay + tdma_packet.fine_delay_time);
			send_packet(tdma_packet, m_master_tr.msg_type, chiptime);
		end
	endtask
	
	task send_packet(tdma_scheme_packet tdma_packet, dsi3_pkg::dsi3_msg_type msg_type, int chiptime);
		dsi3_slave_seq seq = new("slave_response");
		
		// create slave transaction with correct msg_type; tolerance & chiptime from tdma scheme
		if (!m_slave_tr.randomize with {
				msg_type == local::msg_type;
				tolerance_int == local::tdma_packet.tolerance_int;
				data.size() == local::tdma_packet.symbol_count;
				chiptime == local::chiptime;
				chips_per_symbol == 3;
				symbol_coding_error_injection == local::tdma_packet.symbol_coding_error_injection;
				chip_length_error_injection == local::tdma_packet.chip_length_error_injection;
			}) begin
			`uvm_error(this.get_type_name(), "randomization error for slave transaction")
		end
		
		// set data of transaction from the packet
		seq.packet = tdma_packet.packet;
		seq.req = m_slave_tr;
		seq.start(m_sequencer);
	endtask
	
	function time get_delay(dsi3_master_tr m_master_tr, time delay_time);
		time	start_time	= m_master_tr.get_begin_time() + delay_time;
		time    current_time = $time();
		if(start_time > current_time) begin 
			return start_time - current_time;
		end
		else begin
			return time'(-1);
		end
	endfunction
	
	virtual function void reset_dm_pulse_count();
		dm_pulse_cnt = 0;
	endfunction
	
endclass