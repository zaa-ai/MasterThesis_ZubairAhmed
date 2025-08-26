/**
 * Empty default TDMA scheme with 15 packets to be used by upload listener.
 */
class tdma_scheme_empty_default extends tdma_scheme_pdcm;

	function new(string name = "TDMA scheme");
		super.new(name);
		pdcm_period = 1000;
		chiptime = 3;
		repeat(16) begin
			tdma_scheme_packet packet;
			packet = tdma_scheme_packet_pdcm::new_packet(0, 0, 0, dsi3_pkg::SID_0Bit);
			packet.enable = 1'b0;
			add_packet(packet);
		end
	endfunction
endclass

typedef class spi_upload_tdma_packet_seq;
typedef class spi_validate_tdma_scheme_seq;
typedef class spi_tx_crc_request_seq;
typedef class spi_command_frame_seq;

/**
 * Class: tdma_scheme_upload_listener
 * 
 * UVM component, which listens to SPI and RESB transactions and updates expected TDMA schemes accordingly.
 */
class tdma_scheme_upload_listener extends uvm_subscriber #(spi_command_frame_seq);
	
	`uvm_component_utils(tdma_scheme_upload_listener)
	
	uvm_analysis_imp_resb #(digital_signal_tr, tdma_scheme_upload_listener) resb_export;
	
	static tdma_scheme_pdcm schemes[project_pkg::DSI_CHANNELS-1:0];
	
	function new(string name = "tdma_scheme_upload_listener", uvm_component parent);
		super.new(name, parent);
		resb_export = new("resb_export", this);
	endfunction

	virtual function void start_of_simulation_phase(uvm_phase phase);
		set_default_schemes();
	endfunction	
	
	static function void set_default_schemes();
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			tdma_scheme_empty_default scheme = new();
			schemes[channel] = scheme;			
		end
	endfunction
	
	// reset (RESB pin)
	function void write_resb(digital_signal_tr t);
		set_default_schemes();
	endfunction
	
	virtual function void write(spi_command_frame_seq t);
		spi_tx_crc_request_seq crc_seq;
		if($cast(crc_seq, t.commands[$]) == 1) begin
			if(crc_seq.mosi_crc_correct == 1'b1) begin
				foreach(t.commands[i]) begin
					spi_upload_tdma_packet_seq upload_seq;
					spi_validate_tdma_scheme_seq validate_seq;
					if($cast(upload_seq, t.commands[i]) == 1) begin
						received_spi_upload_tdma_packet(upload_seq);
					end
					else if($cast(validate_seq, t.commands[i]) == 1) begin
						received_spi_validate_tdma_scheme(validate_seq);
					end
				end
			end
		end
	endfunction
	
	// upload TDMA packet
	function void received_spi_upload_tdma_packet(spi_upload_tdma_packet_seq seq);
		if(seq.channel_bits[0] == 1'b1)begin
			invalidate(0);
			apply_tdma_packet(0, seq.packet_index, seq.tdma_packet);
		end
		if(seq.channel_bits[1] == 1'b1)begin
			invalidate(1);
			apply_tdma_packet(1, seq.packet_index, seq.tdma_packet);
		end
	endfunction
	
	function void apply_tdma_packet(int channel, int packet_index, tdma_scheme_packet packet);
		schemes[channel].packets[packet_index].earliest_start_time = packet.earliest_start_time;
		schemes[channel].packets[packet_index].latest_start_time = packet.latest_start_time;
		schemes[channel].packets[packet_index].symbol_count = packet.symbol_count;
		schemes[channel].packets[packet_index].id_symbol_count = packet.id_symbol_count;
		schemes[channel].packets[packet_index].enable = 1'b1;
	endfunction
	
	// validate TDMA scheme
	function void received_spi_validate_tdma_scheme(spi_validate_tdma_scheme_seq seq);
		if(seq.channel_bits[0] == 1'b1)begin
			validate(0, seq.packet_count, seq.pdcm_period);
		end
		if(seq.channel_bits[1] == 1'b1)begin
			validate(1, seq.packet_count, seq.pdcm_period);
		end
	endfunction
	
	static function void invalidate(int channel);
		schemes[channel].valid = 1'b0;
		for (int i = 0; i < 16; i++) begin
			schemes[channel].packets[i].enable = 1'b0;
		end
	endfunction
	
	function void validate(int channel, int packet_count, logic[15:0] pdcm_period);
		int normalized_period = int'(pdcm_period);
		if(normalized_period < 100) normalized_period = 100;
		if(normalized_period > 'hFFF0) normalized_period = 'hFFF0;
		
		schemes[channel].pdcm_period = int'(normalized_period);
		for (int i = 0; i < 16; i++) begin
			schemes[channel].packets[i].enable = i < packet_count;
		end
		schemes[channel].valid = schemes[channel].is_valid(packet_count);
	endfunction
endclass
