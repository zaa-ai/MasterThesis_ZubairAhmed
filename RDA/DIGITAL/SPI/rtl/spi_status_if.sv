/**
 * Interface: spi_status_if
 * 
 * interface for status information in SPI
 */
interface spi_status_if import project_pkg::*;();
	
	logic	dsi3_hardware_error;
	logic	overtemperature;
	logic	clkref_failure;
	dsi_logic_t	dsi3_pdcm_data_available;
	dsi_logic_t	dsi3_crm_data_available;
	logic	buffer_fill_warning;
	logic	vcc_uv;
	logic	ldo_uv;
	logic	vrr_nok;
	logic	ecc_failure;
	logic	otp_fail;
	logic	hardware_fail_main_control;
	dsi_logic_t	hardware_fail_dsi3;
	
	logic	hardware_error;
	logic	hardware_fail;
	
	dsi_logic_t	no_tdma_scheme_defined;	
	
	assign	hardware_error = dsi3_hardware_error | clkref_failure | overtemperature|
							vcc_uv | ldo_uv | vrr_nok | 
							otp_fail | ecc_failure;
	
	assign	hardware_fail = (|(hardware_fail_dsi3)) | hardware_fail_main_control;
	
	modport spi (
			input	dsi3_pdcm_data_available, dsi3_crm_data_available, buffer_fill_warning, no_tdma_scheme_defined,
			input	hardware_error, hardware_fail
		);
	
	modport main_control (
			output	vcc_uv, ldo_uv, vrr_nok, overtemperature,
			output	ecc_failure, otp_fail,
			output	hardware_fail_main_control
		);

endinterface
