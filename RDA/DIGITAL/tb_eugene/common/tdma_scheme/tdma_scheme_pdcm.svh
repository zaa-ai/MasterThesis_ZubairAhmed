/**
 * Class: tdma_scheme_pdcm
 * 
 * TDMA scheme for PDCM transmissions
 */
class tdma_scheme_pdcm extends tdma_scheme;

	rand int pdcm_period;
	bit valid;
	
	`uvm_object_utils_begin (tdma_scheme_pdcm)
		`uvm_field_int (pdcm_period, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end
	 
	constraint co_pdcm_period {soft pdcm_period inside {[100:20000]}; }

	function void post_randomize();
		int packet_count;
		super.post_randomize();
		packet_count = get_packet_count();
		if(packet_count > 0) begin
			tdma_scheme_packet last_packet = packets[packet_count-1];
			pdcm_period = last_packet.calculate_endtime_of_packet(chiptime) + $urandom_range(15,200);
		end
	endfunction
	
	virtual function tdma_scheme_packet create_packet();
		tdma_scheme_packet_pdcm packet = new();
		return packet;
	endfunction

	function new(string name = "tdma_scheme_pdcm");
		super.new(name);
	endfunction
	
	/**
	 * Sets SID for all TDMA scheme packets and all its contained dsi3_packets.
	 */
	function void set_source_id_for_all_packets(dsi3_pkg::sid_length_e sid);
		foreach(packets[i]) begin
			tdma_scheme_packet_pdcm pdcm_packet;
			if($cast(pdcm_packet, packets[i]) == 1) begin
				dsi3_pdcm_packet dsi_packet;
				if($cast(dsi_packet, packets[i].packet) == 1) begin
					dsi_packet.source_id_symbols = sid;
				end
				pdcm_packet.id_symbol_count = sid;
			end
		end
	endfunction
	
	function void calculate_start_times(int earliest_start_of_first, int latest_start_of_first);
		int tolerance = latest_start_of_first - earliest_start_of_first;
		real longest_chip_time = ((this.chiptime) * 1.05);
		for (int i=0; i < packets.size(); i++) begin
			if (i==0) begin
				packets[i].earliest_start_time = earliest_start_of_first;
				packets[i].latest_start_time = latest_start_of_first;
			end
			else begin
				packets[i].earliest_start_time = packets[i-1].latest_start_time + ((packets[i-1].symbol_count * 3 + 6 ) * longest_chip_time); // +6 -> inter packet gap of 6*t__chip__
				packets[i].latest_start_time = packets[i].earliest_start_time + tolerance;
			end
		end
	endfunction
	
	/**
	 * Checks if this TDMA scheme is valid.
	 */
	function bit is_valid(int packet_count);
		if(packet_count == 0) begin
			return 1'b0;
		end
		if(packet_count > packets.size()) begin
			return 1'b0;
		end
		for (int i = 0; i < 16; i++) begin
			if(i < packet_count) begin
				if(packets[i].enable == 1'b0) return 1'b0;
				if(packets[i].symbol_count < 4) return 1'b0;
				if(packets[i].earliest_start_time >= packets[i].latest_start_time) return 1'b0;
				if(packets[i].earliest_start_time >= shortint'(pdcm_period)) return 1'b0;
				if(packets[i].latest_start_time >= shortint'(pdcm_period)) return 1'b0;
				if(i+1 < packet_count && packets[i].latest_start_time >= packets[i+1].earliest_start_time) return 1'b0;
			end
			else begin
				// all other packets are expected to be disabled
				if(packets[i] != null && packets[i].enable == 1'b1) return 1'b0;
			end
		end
		return 1'b1;
	endfunction

	virtual function string convert2string();
		string s = "";
		s = $sformatf("TDMA Scheme: %0d packets, period = %0d us", packets.size(), pdcm_period);
		foreach(packets[i]) begin
			tdma_scheme_packet p;
			p = packets[i];
			if(p.enable == 1'b1) begin
				s= {s, $sformatf("\n %2d | Symbols: %3d | %s | Start: %5d - %5d", i, p.symbol_count, p.id_symbol_count.name(), p.earliest_start_time, p.latest_start_time )};
			end
		end
		return s;
	endfunction

endclass


