class upload_random_invalid_tdma_schemes_seq extends base_upload_tdma_schemes_seq;

	`uvm_object_utils(upload_random_invalid_tdma_schemes_seq)
	
	function new(string name = "");
		super.new("upload_random_invalid_tdma_schemes");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("upload random invalid TDMA scheme on all channels", LOG_LEVEL_SEQUENCE);
		
		repeat(100) begin
			upload_tdma_scheme_seq upload_seq;
			tdma_scheme_pdcm valid_scheme = new();
			tdma_scheme_pdcm invalid_scheme = new();
			logic[project_pkg::DSI_CHANNELS-1:0] valid_channels = 2'b11;
			
			if(!valid_scheme.randomize() with {packets.size() > 1;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			if(!invalid_scheme.randomize() with {packets.size() > 1;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			
			invalidate_all_tdma_schemes(1'b0);
			#10us;
			`upload_tdma_scheme_with(valid_scheme, channels == valid_channels;)
			
			make_invalid(invalid_scheme);
			`uvm_create(upload_seq)
			if(!upload_seq.randomize()) `uvm_error(get_type_name(), "failed to randomize") ;
			upload_seq.scheme = invalid_scheme;
			`uvm_send(upload_seq)
			
			valid_channels = valid_channels & ~upload_seq.channels;
			
			check_tdma_upload_status(valid_channels, (upload_seq.channels=='0));
			check_pdcm_periods(valid_channels, valid_scheme.pdcm_period);
            clear_cmd_ign_irq(upload_seq.channels);
			#5us;
		end
		invalidate_all_tdma_schemes(1'b0);
	endtask
	
	function void make_invalid(tdma_scheme_pdcm scheme);
		int packet_index = $urandom_range(scheme.get_packet_count()-1, 0);
		
		randcase
			// symbol count less than 4
			1 : begin
				int invalid_symbol_count = $urandom_range(3, 0);
				scheme.packets[packet_index].symbol_count = invalid_symbol_count;
				`uvm_info(get_type_name(), $sformatf("set symbol count of packet index %0d to %0d", packet_index, invalid_symbol_count), UVM_MEDIUM)
			end
			// not in chronological order
			1 : begin
				int another_packet_index;
				shortint unsigned earliest, latest;
				do another_packet_index = $urandom_range(scheme.get_packet_count()-1, 0);
				while(another_packet_index == packet_index); 
				
				// switch packet start times
				earliest = scheme.packets[packet_index].earliest_start_time;
				latest = scheme.packets[packet_index].earliest_start_time;
				
				scheme.packets[packet_index].earliest_start_time = scheme.packets[another_packet_index].earliest_start_time;
				scheme.packets[packet_index].latest_start_time = scheme.packets[another_packet_index].latest_start_time;
						
				scheme.packets[another_packet_index].earliest_start_time = earliest;
				scheme.packets[another_packet_index].latest_start_time = latest;
				`uvm_info(get_type_name(), $sformatf("switched start times of packets with index %0d and %0d", packet_index, another_packet_index), UVM_MEDIUM)
			end
			// earliest > latest start time
			1 : begin
				int invalid_earliest_start_time = $urandom_range(scheme.pdcm_period, scheme.packets[packet_index].latest_start_time);
				scheme.packets[packet_index].earliest_start_time = invalid_earliest_start_time;
				`uvm_info(get_type_name(), $sformatf("set earliest start time of packet index %0d to %0d", packet_index, invalid_earliest_start_time), UVM_MEDIUM)
			end
			// latest < earliest start time
			1 : begin
				int invalid_latest_start_time = $urandom_range(scheme.packets[packet_index].earliest_start_time, 0);
				scheme.packets[packet_index].latest_start_time = invalid_latest_start_time;
				`uvm_info(get_type_name(), $sformatf("set latest start time of packet index %0d to %0d", packet_index, invalid_latest_start_time), UVM_MEDIUM)
			end
			// period lower earliest start time
			1 : begin
				int invalid_period = int'(scheme.packets[packet_index].earliest_start_time);
				scheme.pdcm_period = invalid_period;
				`uvm_info(get_type_name(), $sformatf("set PDCM period to %0d (earliest start time of packet %0d)", invalid_period, packet_index), UVM_MEDIUM)
			end
			// period lower latest start time
			1 : begin
				int invalid_period = int'(scheme.packets[packet_index].latest_start_time);
				scheme.pdcm_period = invalid_period;
				`uvm_info(get_type_name(), $sformatf("set PDCM period to %0d (latest start time of packet %0d)", invalid_period, packet_index), UVM_MEDIUM)
			end
		endcase
	endfunction
endclass

