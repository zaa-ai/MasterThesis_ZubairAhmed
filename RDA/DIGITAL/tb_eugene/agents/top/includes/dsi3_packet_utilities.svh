
function void create_valid_CRM_packets_with_data(ref dsi3_crm_packet packets[$], input logic[project_pkg::DSI_CHANNELS-1:0] channels = {project_pkg::DSI_CHANNELS{1'b1}});
	for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
		if(channels[channel] == 1'b1) begin
			dsi3_crm_packet next_packet = new();
			if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
			packets.push_back(next_packet);
			add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1)));
		end
	end
endfunction

function void create_CRM_packets_without_data(int packet_count = 1, logic[project_pkg::DSI_CHANNELS-1:0] channels = {project_pkg::DSI_CHANNELS{1'b1}});
	repeat(packet_count) begin
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel] == 1'b1) begin
				add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
			end
		end
	end
endfunction

function void create_valid_PDCM_packets_with_data(ref dsi3_pdcm_packet packets[$], input logic[project_pkg::DSI_CHANNELS-1:0] channels = {project_pkg::DSI_CHANNELS{1'b1}}, int packet_count = 1, int symbol_count = 8, dsi3_pkg::sid_length_e sid = dsi3_pkg::SID_8Bit);
	for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
		if(channels[channel] == 1'b1) begin
			dsi3_pdcm_packet pdcm_packets[$];
			tdma_scheme scheme;
			repeat(packet_count) begin
				dsi3_pdcm_packet packet = create_random_packet(symbol_count, sid);
				pdcm_packets.push_back(packet);
				packets.push_back(packet);
			end
			scheme = tdma_scheme_pdcm_factory::multiple_pdcm_packets(pdcm_packets);
			add_slave_pdcm_scheme(channel, scheme);
		end
	end
endfunction

function void add_random_packets_for_all_channels(ref dsi3_crm_packet packets[$], input int chiptime=3, dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US);
	for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
		dsi3_crm_packet next_packet = new();
		if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
		packets.push_back(next_packet);
		add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1), chiptime, bit_time));
	end
endfunction

function dsi3_pdcm_packet create_random_packet(int symbol_count, dsi3_pkg::sid_length_e sid);
	dsi3_pdcm_packet packet = new();
	if(!packet.randomize() with {data.size() == symbol_count; source_id_symbols == sid;}) `uvm_error(this.get_name(), "randomization error")
	return packet;
endfunction

function tdma_scheme_packet create_crm_noise_packet(int noise_symbols);
	tdma_scheme_packet noise_packet = tdma_scheme_packet_crm::new_packet(265, 265, noise_symbols);
	dsi3_packet noise_data_packet = new();
	if(!noise_data_packet.randomize() with {data.size() == noise_symbols;}) `uvm_error(this.get_name(), "randomization error")
	noise_packet.packet = noise_data_packet;
	return noise_packet;
endfunction

function void random_slave_scheme(int start_time, int min_symbols, int max_symbols, int chip_time, ref dsi3_packet packets[project_pkg::DSI_CHANNELS-1:0]);
	for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
		random_slave_scheme_for_channel(channel, start_time, min_symbols, max_symbols, chip_time, packets[project_pkg::DSI_CHANNELS-1:0]);
	end
endfunction

function void random_slave_scheme_for_channel(int channel, int start_time, int min_symbols, int max_symbols, int chip_time, ref dsi3_packet packets[project_pkg::DSI_CHANNELS-1:0]);
	dsi3_packet next_packet = new();
	tdma_scheme scheme = tdma_scheme_crm::default_scheme(chip_time);
	if(!next_packet.randomize() with {data.size() inside {[min_symbols:max_symbols]};}) `uvm_error(this.get_name(), "randomization error")
	scheme.packets[0].packet.data = next_packet.data;
	scheme.packets[0].earliest_start_time = start_time;
	scheme.packets[0].latest_start_time = start_time;
	packets[channel]= next_packet;
	add_slave_crm_scheme(channel, scheme);
endfunction

function void check_clkref_error_packages(spi_read_crm_data_packets_seq read, dsi3_crm_packet packets[$]);
	for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
		dsi_response_flags expected_flags[$] = {CE};
		if(!packets[channel].crc_correct) expected_flags.push_back(CRC);
		read.expect_flags( 2'(channel), expected_flags);
		read.expect_packet(2'(channel), packets[channel]);
	end
endfunction

/**
 * Checks contents of CMD_HIGH and CMD_LOW registers. 
 */
task check_DSI_CMD_HIGH_LOW(int channel, dsi3_packet packet);
	uvm_reg_data_t value;
	
	regmodel.DSI[channel].DSI3_channel_registers.CRM_WORD1.read(status, value);
	if(value != 64'(packet.get_word(0))) begin
		`uvm_error(this.get_name(), $sformatf("Unexpected value contained in CRM_WORD1 register of channel %0d, expected %0h, got %0h.", channel, packet.get_word(0), value)) 
		log_sim_check("CRM_WORD1", .status("FAIL"));
	end 
	else begin
		log_sim_check("CRM_WORD1", .status("PASS"));			
	end
	
	regmodel.DSI[channel].DSI3_channel_registers.CRM_WORD2.read(status, value);
	if(value != 64'(packet.get_word(1))) begin
		`uvm_error(this.get_name(), $sformatf("Unexpected value contained in CRM_WORD2 register of channel %0d, expected %0h, got %0h.", channel, packet.get_word(1), value)) 
		log_sim_check("CRM_WORD2", .status("FAIL"));
	end
	else begin
		log_sim_check("CRM_WORD2", .status("PASS"));
	end
endtask

task check_PKG_STAT(int channel, bit crc_error);
	uvm_reg_data_t value;
	logic[15:0] pkg_stat = get_expected_pkg_stat(crc_error);
	
	regmodel.DSI[channel].DSI3_channel_registers.PACKET_STAT.read(status, value);
	if(value != $size(uvm_reg_data_t)'(pkg_stat)) begin
		`uvm_error(this.get_type_name(), $sformatf("Unexpected value in PACKET_STAT of channel %0d, expected 0x%0h, got 0x%0h", channel, pkg_stat, value))
		log_sim_check("PACKET_STAT", .status("FAIL"));
	end
	else begin
		log_sim_check("PACKET_STAT", .status("PASS"));
	end
endtask

function logic[15:0] get_expected_pkg_stat(bit crc_error);
	logic[15:0] pkg_stat;
	flags_container #(dsi_response_flags) flags = new();
	flags.set_value(CRC, crc_error);
	pkg_stat = 16'(flags.get_values());
	pkg_stat += 16'(8); // symbol count
	pkg_stat[15] = 1'b0; // no PSE
	return pkg_stat;
endfunction
