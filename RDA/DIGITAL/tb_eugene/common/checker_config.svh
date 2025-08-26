
/**
 * Global config object for different checkers.
 */
class checker_config extends uvm_object;

	// enables mirroring check in behaviour_checker
	bit	enable_mirroring_check = 1'b1;
	// enables check of MISO SPI CRC
	bit	enable_spi_miso_crc_check = 1'b1;
	// enables automatic check for IC status word (in read status commands and in first MISO word of a new frame)  
	bit enable_status_word_check = 1'b1; 
	// enables automatic check for hardware errors in behaviour_checker
	bit enable_hardware_error_check = 1'b1; 
	// enable measure of each PDCM pulse in dsi3_master_transmission_checker
	bit enable_measure_pdcm_pulse = 1'b1;
	// enable automatic check of PDCM period time
	bit enable_check_pdcm_period = 1'b1;
	// enables printing of PDCM read frame 
	bit	enable_print_pdcm_read = 1'b1;
	// enable measure of each Discovery mode pulse in dsi3_master_transmission_checker
	bit enable_measure_discovery_pulse = 1'b0;
	
	// generate an error if size of master transaction is unknown (not PDCM and not CRM)
	bit enable_error_if_unknown_transaction_size = 1'b1;
	
	bit[project_pkg::DSI_CHANNELS-1:0] enable_master_transmission_checker = {project_pkg::DSI_CHANNELS{1'b1}};
	
	// expect a CE flag in received DSI packet
	bit expect_CRM_clock_ref_error_in_dsi_packet = 1'b0;
	// expect a VE flag in received DSI packet
	bit[project_pkg::DSI_CHANNELS-1:0] expect_CRM_voltage_error_in_dsi_packet = 'b0;
	// expect a SE flag in received DSI packet
	bit[project_pkg::DSI_CHANNELS-1:0] expect_CRM_symbol_coding_error_in_dsi_packet = 'b0;
	
	// expect a CE flag in received DSI packet
	int expect_PDCM_clock_ref_error_in_dsi_packet[project_pkg::DSI_CHANNELS-1:0][$];
	// expect a VE flag in received DSI packet
	int expect_PDCM_voltage_error_in_dsi_packet[project_pkg::DSI_CHANNELS-1:0][$];
	// expect a SE flag in received DSI packet
	int expect_PDCM_symbol_coding_error_in_dsi_packet[project_pkg::DSI_CHANNELS-1:0][$];
	
	static protected checker_config configuration;

	protected function new(string name = "");
		super.new(name);
	endfunction
	
	static function checker_config get();
		if (configuration == null) begin
			configuration = new();
		end
		return configuration;
	endfunction
	
	function void set_master_transmission_checker_enable(int channel, bit enable);
		enable_master_transmission_checker[channel] = enable;
	endfunction
	
	function void enable_all_master_transmission_checkers();
		enable_master_transmission_checker = {project_pkg::DSI_CHANNELS{1'b1}};
	endfunction
	
	function void disable_all_master_transmission_checkers();
		enable_master_transmission_checker = {project_pkg::DSI_CHANNELS{1'b0}};
	endfunction
	
endclass 
