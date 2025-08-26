typedef enum logic[2:0]{
	NONE_2_RAM,
	SYSTEM_2_RAM,
	SPI_COMMAND_BUFFER_2_RAM,
	DSI_COMMAND_BUFFER_2_RAM,
	DSI_PDCM_DATA_BUFFER_2_RAM,
	DSI_CRM_DATA_BUFFER_2_RAM,
	DSI_TDMA_2_RAM
} elip_ram_selector_t;

`define elip_ram_assignment(_if_) elip_ram.addr = _if_``.addr - elip_addr_t'(BASE_ADDR_RAM); \
elip_ram.data_write = _if_``.data_write; \
elip_ram.wr = _if_``.wr; \
elip_ram.rd = _if_``.rd;

/**
 * Module: elip_ram_access_arbiter
 *
 * Module for arbitrating elip accesses to RAM from buffers and SPI/JTAG
 */
module elip_ram_access_arbiter import project_pkg::*; (
		elip_full_if.slave	elip_system,
		elip_full_if.slave	elip_spi_command_buffer,
		elip_full_if.slave	elip_dsi_command_buffer[DSI_CHANNELS-1:0],
		elip_full_if.slave	elip_dsi_tdma[DSI_CHANNELS-1:0],
		elip_full_if.slave	elip_dsi_pdcm_data_buffer[DSI_CHANNELS-1:0],
		elip_full_if.slave	elip_dsi_crm_data_buffer[DSI_CHANNELS-1:0],
		elip_full_if.master	elip_ram
	);

	elip_ram_selector_t	selector;

	/*###   DSI command buffer   ######################################################*/
	dsi_logic_t dsi_command_buffer_rd, dsi_command_buffer_wr, dsi_command_buffer_ready;
	elip_addr_t	dsi_command_buffer_addr[DSI_CHANNELS-1:0];
	data_ecc_t	dsi_command_buffer_data_write[DSI_CHANNELS-1:0];

	dsi_logic_t	dsi_command_buffer_access_grant;

	generate
		genvar i;
		for (i=0; i<DSI_CHANNELS; i++) begin : generate_dsi_elip_signals_for_dsi_command_buffer
			assign	dsi_command_buffer_rd[i] = elip_dsi_command_buffer[i].rd;
			assign	dsi_command_buffer_wr[i] = elip_dsi_command_buffer[i].wr;
			assign	dsi_command_buffer_addr[i] = elip_dsi_command_buffer[i].addr;
			assign	elip_dsi_command_buffer[i].ready = dsi_command_buffer_ready[i];
			assign	dsi_command_buffer_data_write[i] = elip_dsi_command_buffer[i].data_write;

			assign	elip_dsi_command_buffer[i].data_read = elip_ram.data_read;
		end
	endgenerate

	logic	dsi_command_buffer_access;
	assign 	dsi_command_buffer_access = (|(dsi_command_buffer_rd)) | (|(dsi_command_buffer_wr));

	/*###   DSI PDCM data buffer   ######################################################*/
	dsi_logic_t dsi_pdcm_data_buffer_rd, dsi_pdcm_data_buffer_wr, dsi_pdcm_data_buffer_ready;
	elip_addr_t	dsi_pdcm_data_buffer_addr[DSI_CHANNELS-1:0];
	data_ecc_t	dsi_pdcm_data_buffer_data_write[DSI_CHANNELS-1:0];

	dsi_logic_t	dsi_pdcm_data_buffer_access_grant;

	generate
		genvar j;
		for (j=0; j<DSI_CHANNELS; j++) begin : generate_dsi_elip_signals_for_dsi_pdcm_data_buffer
			assign	dsi_pdcm_data_buffer_rd[j] = elip_dsi_pdcm_data_buffer[j].rd;
			assign	dsi_pdcm_data_buffer_wr[j] = elip_dsi_pdcm_data_buffer[j].wr;
			assign	dsi_pdcm_data_buffer_addr[j] = elip_dsi_pdcm_data_buffer[j].addr;
			assign	elip_dsi_pdcm_data_buffer[j].ready = dsi_pdcm_data_buffer_ready[j];
			assign	dsi_pdcm_data_buffer_data_write[j] = elip_dsi_pdcm_data_buffer[j].data_write;

			assign	elip_dsi_pdcm_data_buffer[j].data_read = elip_ram.data_read;
		end
	endgenerate

	logic	dsi_pdcm_data_buffer_read_access, dsi_pdcm_data_buffer_write_access;
	assign	dsi_pdcm_data_buffer_read_access = |(dsi_pdcm_data_buffer_rd);
	assign	dsi_pdcm_data_buffer_write_access = |(dsi_pdcm_data_buffer_wr);
	
	/*###   DSI CRM data buffer   ######################################################*/
	dsi_logic_t dsi_crm_data_buffer_rd, dsi_crm_data_buffer_wr, dsi_crm_data_buffer_ready;
	elip_addr_t	dsi_crm_data_buffer_addr[DSI_CHANNELS-1:0];
	data_ecc_t	dsi_crm_data_buffer_data_write[DSI_CHANNELS-1:0];

	dsi_logic_t	dsi_crm_data_buffer_access_grant;

	generate
		genvar l;
		for (l=0; l<DSI_CHANNELS; l++) begin : generate_dsi_elip_signals_for_dsi_crm_data_buffer
			assign	dsi_crm_data_buffer_rd[l] = elip_dsi_crm_data_buffer[l].rd;
			assign	dsi_crm_data_buffer_wr[l] = elip_dsi_crm_data_buffer[l].wr;
			assign	dsi_crm_data_buffer_addr[l] = elip_dsi_crm_data_buffer[l].addr;
			assign	elip_dsi_crm_data_buffer[l].ready = dsi_crm_data_buffer_ready[l];
			assign	dsi_crm_data_buffer_data_write[l] = elip_dsi_crm_data_buffer[l].data_write;

			assign	elip_dsi_crm_data_buffer[l].data_read = elip_ram.data_read;
		end
	endgenerate

	logic	dsi_crm_data_buffer_read_access, dsi_crm_data_buffer_write_access;
	assign	dsi_crm_data_buffer_read_access = |(dsi_crm_data_buffer_rd);
	assign	dsi_crm_data_buffer_write_access = |(dsi_crm_data_buffer_wr);
	
	/*###   DSI TDMA buffer   ######################################################*/
	dsi_logic_t dsi_tdma_rd, dsi_tdma_wr, dsi_tdma_ready;
	elip_addr_t	dsi_tdma_addr[DSI_CHANNELS-1:0];
	data_ecc_t	dsi_tdma_data_write[DSI_CHANNELS-1:0];

	dsi_logic_t	dsi_tdma_access_grant;

	generate
		genvar k;
		for (k=0; k<DSI_CHANNELS; k++) begin : generate_dsi_elip_signals_for_dsi_tdma
			assign	dsi_tdma_rd[k] = elip_dsi_tdma[k].rd;
			assign	dsi_tdma_wr[k] = elip_dsi_tdma[k].wr;
			assign	dsi_tdma_addr[k] = elip_dsi_tdma[k].addr;
			assign	elip_dsi_tdma[k].ready = dsi_tdma_ready[k];
			assign	dsi_tdma_data_write[k] = elip_dsi_tdma[k].data_write;

			assign	elip_dsi_tdma[k].data_read = elip_ram.data_read;
		end
	endgenerate

	logic	dsi_tdma_access;
	assign	dsi_tdma_access = (|(dsi_tdma_rd)) |  (|(dsi_tdma_wr));

	/*###   SPI   ######################################################*/
	logic	elip_spi_command_buffer_access;
	assign	elip_spi_command_buffer_access = elip_spi_command_buffer.wr | elip_spi_command_buffer.rd;

	/*###   selector   ######################################################*/
	always_comb begin
		if ((elip_system.rd == 1'b1) || (elip_system.wr == 1'b1)) // access to RAM from SPI or JTAG
			selector = SYSTEM_2_RAM;
		else begin
			if (dsi_pdcm_data_buffer_read_access == 1'b1) begin
				selector = DSI_PDCM_DATA_BUFFER_2_RAM;
			end
			else begin
				if (dsi_crm_data_buffer_read_access == 1'b1) begin
					selector = DSI_CRM_DATA_BUFFER_2_RAM;
				end
				else begin
					if (elip_spi_command_buffer_access) begin
						selector = SPI_COMMAND_BUFFER_2_RAM;
					end
					else begin
						if (dsi_pdcm_data_buffer_write_access == 1'b1) begin
							selector = DSI_PDCM_DATA_BUFFER_2_RAM;
						end
						else begin
							if (dsi_crm_data_buffer_write_access == 1'b1) begin
								selector = DSI_CRM_DATA_BUFFER_2_RAM;
							end
							else begin
								if (dsi_command_buffer_access == 1'b1) begin
									selector = DSI_COMMAND_BUFFER_2_RAM;
								end
								else begin
									if (dsi_tdma_access == 1'b1) begin
										selector = DSI_TDMA_2_RAM;	
									end
									else begin
										selector = NONE_2_RAM;
									end
								end
							end
						end
					end
				end
			end
		end
	end

    dsi_logic_t dsi_command_buffer_access_granted;
    dsi_logic_t dsi_pdcm_data_buffer_access_granted;
    dsi_logic_t dsi_crm_data_buffer_access_granted;
    dsi_logic_t dsi_tdma_access_granted;
    
    generate
        genvar channel;
        for (channel = 0; channel < DSI_CHANNELS; channel++) begin : generate_dsi_command_buffer_access_grant
            assign  dsi_command_buffer_access_granted[channel]   = ((dsi_command_buffer_wr == '0)    ? dsi_command_buffer_rd[channel]   : 1'b0) | dsi_command_buffer_wr[channel];
            assign  dsi_pdcm_data_buffer_access_granted[channel] = ((dsi_pdcm_data_buffer_rd == '0 ) ? dsi_pdcm_data_buffer_wr[channel] : 1'b0) | dsi_pdcm_data_buffer_rd[channel];
            assign  dsi_crm_data_buffer_access_granted[channel]  = ((dsi_crm_data_buffer_rd == '0)   ? dsi_crm_data_buffer_wr[channel]  : 1'b0) | dsi_crm_data_buffer_rd[channel];
            assign  dsi_tdma_access_granted[channel]             = ((dsi_tdma_rd == '0)              ? dsi_tdma_wr[channel]             : 1'b0) | dsi_tdma_rd[channel];
        end
    endgenerate
    
    always_comb begin
        dsi_command_buffer_access_grant = '0;
        for (dsi_logic_t channel=dsi_logic_t'(DSI_CHANNELS-1); channel<dsi_logic_t'(DSI_CHANNELS); channel-=dsi_logic_t'(1)) begin
            if (dsi_command_buffer_access_granted[channel] == 1'b1) 
                dsi_command_buffer_access_grant = channel;
        end
    end
    
    always_comb begin
        dsi_pdcm_data_buffer_access_grant = '0;
        for (dsi_logic_t channel=dsi_logic_t'(DSI_CHANNELS-1); channel<dsi_logic_t'(DSI_CHANNELS); channel-=dsi_logic_t'(1)) begin
            if (dsi_pdcm_data_buffer_access_granted[channel] == 1'b1) 
                dsi_pdcm_data_buffer_access_grant = channel;
        end
    end
    
    always_comb begin
        dsi_crm_data_buffer_access_grant = '0;
        for (dsi_logic_t channel=dsi_logic_t'(DSI_CHANNELS-1); channel<dsi_logic_t'(DSI_CHANNELS); channel-=dsi_logic_t'(1)) begin
            if (dsi_crm_data_buffer_access_granted[channel] == 1'b1) 
                dsi_crm_data_buffer_access_grant = channel;
        end
    end
    
    always_comb begin
        dsi_tdma_access_grant = '0;
        for (dsi_logic_t channel=dsi_logic_t'(DSI_CHANNELS-1); channel<dsi_logic_t'(DSI_CHANNELS); channel-=dsi_logic_t'(1)) begin
            if (dsi_tdma_access_granted[channel] == 1'b1) 
                dsi_tdma_access_grant = channel;
        end
    end
	
	/*###   ELIP for RAM assignments   ######################################################*/
	always_comb begin
		case (selector)
			SYSTEM_2_RAM : begin
				//`elip_ram_assignment(elip_system)
				elip_ram.addr = elip_system.addr - elip_addr_t'(BASE_ADDR_RAM);
				elip_ram.data_write = elip_system.data_write;
				elip_ram.wr = elip_system.wr;
				elip_ram.rd = elip_system.rd;
			end
			SPI_COMMAND_BUFFER_2_RAM : begin
				//`elip_ram_assignment(elip_spi_command_buffer)
				elip_ram.addr = elip_spi_command_buffer.addr - elip_addr_t'(BASE_ADDR_RAM);
				elip_ram.data_write = elip_spi_command_buffer.data_write;
				elip_ram.wr = elip_spi_command_buffer.wr;
				elip_ram.rd = elip_spi_command_buffer.rd;
			end
			DSI_COMMAND_BUFFER_2_RAM : begin
				elip_ram.addr = dsi_command_buffer_addr[dsi_command_buffer_access_grant] - elip_addr_t'(BASE_ADDR_RAM);
				elip_ram.data_write = dsi_command_buffer_data_write[dsi_command_buffer_access_grant];
				elip_ram.wr = dsi_command_buffer_wr[dsi_command_buffer_access_grant];
				elip_ram.rd = dsi_command_buffer_rd[dsi_command_buffer_access_grant];
			end
			DSI_PDCM_DATA_BUFFER_2_RAM: begin
				elip_ram.addr = dsi_pdcm_data_buffer_addr[dsi_pdcm_data_buffer_access_grant] - elip_addr_t'(BASE_ADDR_RAM);
				elip_ram.data_write = dsi_pdcm_data_buffer_data_write[dsi_pdcm_data_buffer_access_grant];
				elip_ram.wr = dsi_pdcm_data_buffer_wr[dsi_pdcm_data_buffer_access_grant];
				elip_ram.rd = dsi_pdcm_data_buffer_rd[dsi_pdcm_data_buffer_access_grant];
			end
			DSI_CRM_DATA_BUFFER_2_RAM: begin
				elip_ram.addr = dsi_crm_data_buffer_addr[dsi_crm_data_buffer_access_grant] - elip_addr_t'(BASE_ADDR_RAM);
				elip_ram.data_write = dsi_crm_data_buffer_data_write[dsi_crm_data_buffer_access_grant];
				elip_ram.wr = dsi_crm_data_buffer_wr[dsi_crm_data_buffer_access_grant];
				elip_ram.rd = dsi_crm_data_buffer_rd[dsi_crm_data_buffer_access_grant];
			end
			DSI_TDMA_2_RAM: begin
				elip_ram.addr = dsi_tdma_addr[dsi_tdma_access_grant] - elip_addr_t'(BASE_ADDR_RAM);
				elip_ram.data_write = dsi_tdma_data_write[dsi_tdma_access_grant];
				elip_ram.wr = dsi_tdma_wr[dsi_tdma_access_grant];
				elip_ram.rd = dsi_tdma_rd[dsi_tdma_access_grant];
			end
			default: begin
				elip_ram.addr = '0;
				elip_ram.data_write = EMPTY_DATA;
				elip_ram.wr = 1'b0;
				elip_ram.rd = 1'b0;
			end
		endcase
	end

	/*###   READY assignments   ######################################################*/
	always_comb begin
		dsi_command_buffer_ready = '0;
		dsi_pdcm_data_buffer_ready = '0;
		dsi_crm_data_buffer_ready = '0;
		dsi_tdma_ready = '0;
		elip_system.ready = 1'b0;
		elip_spi_command_buffer.ready = 1'b0;
		case (selector)
			SYSTEM_2_RAM : begin
				elip_system.ready = elip_ram.ready;
			end
			SPI_COMMAND_BUFFER_2_RAM : begin
				elip_spi_command_buffer.ready = elip_ram.ready;
			end
			DSI_COMMAND_BUFFER_2_RAM : begin
				dsi_command_buffer_ready[dsi_command_buffer_access_grant] = elip_ram.ready;
			end
			DSI_PDCM_DATA_BUFFER_2_RAM: begin
				dsi_pdcm_data_buffer_ready[dsi_pdcm_data_buffer_access_grant] = elip_ram.ready;
			end
			DSI_CRM_DATA_BUFFER_2_RAM: begin
				dsi_crm_data_buffer_ready[dsi_crm_data_buffer_access_grant] = elip_ram.ready;
			end
			DSI_TDMA_2_RAM: begin
				dsi_tdma_ready[dsi_tdma_access_grant] = elip_ram.ready;
			end
		endcase
	end

	/*###   data_read assignments   ######################################################*/
	assign	elip_system.data_read = elip_ram.data_read;
	assign	elip_spi_command_buffer.data_read = elip_ram.data_read;

endmodule


