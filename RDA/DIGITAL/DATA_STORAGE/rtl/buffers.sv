`include "global_defines.sv"

/**
 * Module: buffers
 *
 * includes all buffers of the design
 */
module buffers import project_pkg::*; #(
		parameter ADDR_WIDTH = 16
		)(
			clk_reset_if.slave	clk_rst,
			buffer_reader_if.slave	command_reader,
			buffer_writer_if.slave	command_writer,
			buffer_reader_if.slave	dsi3_command_reader[DSI_CHANNELS-1:0],
			buffer_writer_if.slave	dsi3_command_writer[DSI_CHANNELS-1:0],
			buffer_reader_if.slave	dsi3_pdcm_data_reader,
            pdcm_buffer_writer_if.slave	dsi3_pdcm_data_writer[DSI_CHANNELS-1:0],
			buffer_reader_if.slave	dsi3_crm_data_reader,
			buffer_writer_if.slave	dsi3_crm_data_writer[DSI_CHANNELS-1:0],
			elip_full_if.master		elip_command_buffer,
			elip_full_if.master		elip_dsi3_command_buffer[DSI_CHANNELS-1:0],
			elip_full_if.master		elip_dsi3_pdcm_data_buffer[DSI_CHANNELS-1:0],
			elip_full_if.master		elip_dsi3_crm_data_buffer[DSI_CHANNELS-1:0],
			elip_if.slave			elip_registers,
			input	dsi_select_t	i_dsi3_pdcm_data_reader_channel_select,
			input	dsi_select_t	i_dsi3_crm_data_reader_channel_select,
			output	elip_data_t		o_elip_registers_data_out,
			output	logic			o_interrupt,
			pad_int_if.master		bfwb_pad,
			pad_int_if.master		dab_pad,
			output	dsi_logic_t		o_dsi3_pdcm_data_available,
			output	dsi_logic_t		o_dsi3_crm_data_available,
			output	logic			o_buffer_fill_warning,
			ecc_error_if.master		spi_cmd_buf_ecc_error,
			ecc_error_if.master		dsi_cmd_buf_ecc_error,
			ecc_error_if.master		dsi_crm_data_buf_ecc_error,
			ecc_error_if.master		dsi_pdcm_data_buf_ecc_error
		);

	elip_data_t	interrupt_registers_out, command_buffer_registers_out;
	elip_data_t	dsi3_command_buffer_registers_out[DSI_CHANNELS-1:0];
	elip_data_t	dsi3_pdcm_data_buffer_registers_out[DSI_CHANNELS-1:0];
	elip_data_t	dsi3_crm_data_buffer_registers_out[DSI_CHANNELS-1:0];
	dsi_logic_t dsi3_command_buffer_full, dsi3_pdcm_data_buffer_full, dsi3_crm_data_buffer_full;
	dsi_logic_t dsi3_command_buffer_full_warn, dsi3_pdcm_data_buffer_full_warn, dsi3_crm_data_buffer_full_warn;
	logic	dab, dab_next, bfwb, bfwb_next;
	dsi_logic_t	da_dsi3_pdcm_data;
	dsi_logic_t	da_dsi3_crm_data;

	/*###   registers   ######################################################*/
	`include "buffer_interrupt_registers_if_inst.sv"
	buffer_interrupt_registers #(
			.base_addr                                (BASE_ADDR_BUFFER_IRQS                   ),
			.addr_width                               (ADDR_WIDTH                              )
		) i_buffer_interrupt_registers (
			.clk_rst                                  (clk_rst                                 ),
			.addr                                     (elip_registers.addr                     ),
			.data_in                                  (elip_registers.data_write               ),
			.wr                                       (elip_registers.wr                       ),
			.rd                                       (elip_registers.rd                       ),
			.data_out                                 (interrupt_registers_out                 ),
			.buffer_interrupt_registers_BUF_IRQ_STAT  (buffer_interrupt_registers_BUF_IRQ_STAT.master ),
			.buffer_interrupt_registers_BUF_IRQ_MASK  (buffer_interrupt_registers_BUF_IRQ_MASK.master ),
			.buffer_interrupt_registers_BUF_FILL_WARN (buffer_interrupt_registers_BUF_FILL_WARN.master));

	assign	o_interrupt = |(buffer_interrupt_registers_BUF_IRQ_STAT.value & buffer_interrupt_registers_BUF_IRQ_MASK.value);

	assign	buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE_set  = command_writer.full;
	assign	buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE_in   = 1'b1;
	assign	buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE_set  = |(dsi3_command_buffer_full);
	assign	buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE_in   = buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE | dsi3_command_buffer_full;
	assign	buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE_set = |(dsi3_pdcm_data_buffer_full);
	assign	buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE_in  = buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE | dsi3_pdcm_data_buffer_full;
	assign	buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE_set  = |(dsi3_crm_data_buffer_full);
	assign	buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE_in   = buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE | dsi3_crm_data_buffer_full;
	assign	buffer_interrupt_registers_BUF_FILL_WARN.DSI_CMD_FW_in  = dsi3_command_buffer_full_warn;
	assign	buffer_interrupt_registers_BUF_FILL_WARN.DSI_PDCM_FW_in = dsi3_pdcm_data_buffer_full_warn;
	assign	buffer_interrupt_registers_BUF_FILL_WARN.DSI_CRM_FW_in  = dsi3_crm_data_buffer_full_warn;
	assign	buffer_interrupt_registers_BUF_FILL_WARN.SPI_CMD_FW_in  = command_writer.nearly_full;

	/*###   buffers   ######################################################*/
	buffer_reader_if	dsi3_pdcm_data_readers[DSI_CHANNELS-1:0]();
	buffer_reader_if	dsi3_crm_data_readers[DSI_CHANNELS-1:0]();
	buffer_reader_demux i_dsi3_pdcm_reader_demux (
			.reader          (dsi3_pdcm_data_reader  ),
			.readers         (dsi3_pdcm_data_readers.master ),
			.channel_select  (i_dsi3_pdcm_data_reader_channel_select ));
	buffer_reader_demux i_dsi3_crm_reader_demux (
			.reader          (dsi3_crm_data_reader  ),
			.readers         (dsi3_crm_data_readers.master ),
			.channel_select  (i_dsi3_crm_data_reader_channel_select ));

	buffer #(
			.BASE_ADDR                  (BASE_ADDR_SPI_CMD_STAT    ),
			.ADDR_WIDTH                 (ADDR_WIDTH                ),
			.BUFFER_OFFSET_ADDRESS      (BASE_ADDR_SPI_CMD_BUF     ),
			.BUFFER_SIZE                (SIZE_SPI_CMD_BUF          ),
			.PRIORITY_READ              (1'b0                      )
		) i_command_buffer (
			.clk_rst                    (clk_rst                   ),
			.reader                     (command_reader            ),
			.writer                     (command_writer            ),
			.elip                       (elip_command_buffer       ),
			.elip_registers             (elip_registers            ),
			.o_elip_registers_data_out  (command_buffer_registers_out ),
			.o_data_available           (                          ),
			.ecc_error                  (spi_cmd_buf_ecc_error     ));
	
	ecc_error_if	int_dsi_cmd_ecc_error[DSI_CHANNELS-1:0] ();
	ecc_error_if	int_dsi3_pdcm_data_ecc_error[DSI_CHANNELS-1:0] ();
	ecc_error_if	int_dsi3_crm_data_ecc_error[DSI_CHANNELS-1:0] ();

	generate
		for (genvar i=0; i< DSI_CHANNELS; i++) begin : generate_dsi_buffers
			buffer #(
				.BASE_ADDR                  (BASE_ADDR_DSI_CMD_STAT[i]),
				.ADDR_WIDTH                 (ADDR_WIDTH                ),
				.BUFFER_OFFSET_ADDRESS      (BASE_ADDR_DSI_CMD_BUF[i]),
				.BUFFER_SIZE                (SIZE_DSI_CMD_BUF               ),
				.PRIORITY_READ              (1'b0             )
			) i_dsi3_command_buffer (
				.clk_rst                    (clk_rst                              ),
				.reader                     (dsi3_command_reader[i]               ),
				.writer                     (dsi3_command_writer[i]               ),
				.elip                       (elip_dsi3_command_buffer[i]          ),
				.elip_registers             (elip_registers                       ),
				.o_elip_registers_data_out  (dsi3_command_buffer_registers_out[i] ),
				.o_data_available           (                                     ),
				.ecc_error                  (int_dsi_cmd_ecc_error[i].master      ));
			
			assign	dsi3_command_buffer_full[i] = dsi3_command_writer[i].full;
			assign	dsi3_command_buffer_full_warn[i] = dsi3_command_writer[i].nearly_full;
			
			pdcm_buffer #(
				.BASE_ADDR                  (BASE_ADDR_DSI_PDCM_STAT[i]),
				.ADDR_WIDTH                 (ADDR_WIDTH                        ),
				.BUFFER_OFFSET_ADDRESS      (BASE_ADDR_DSI_PDCM_BUF[i]         ),
				.BUFFER_SIZE                (SIZE_DSI_PDCM_BUF                 ),
				.PRIORITY_READ              (1'b1                              )
			) i_dsi3_pdcm_data_buffer (
				.clk_rst                    (clk_rst                           ),
				.reader                     (dsi3_pdcm_data_readers[i].slave        ),
				.writer                     (dsi3_pdcm_data_writer[i]               ),
				.elip                       (elip_dsi3_pdcm_data_buffer[i]     ),
				.elip_registers             (elip_registers                    ),
				.o_elip_registers_data_out  (dsi3_pdcm_data_buffer_registers_out[i] ),
				.o_data_available           (da_dsi3_pdcm_data[i]                   ),
				.ecc_error                  (int_dsi3_pdcm_data_ecc_error[i].master  ));
			
			buffer #(
				.BASE_ADDR                  (BASE_ADDR_DSI_CRM_STAT[i]         ),
				.ADDR_WIDTH                 (ADDR_WIDTH                        ),
				.BUFFER_OFFSET_ADDRESS      (BASE_ADDR_DSI_CRM_BUF[i]          ),
				.BUFFER_SIZE                (SIZE_DSI_CRM_BUF                  ),
				.PRIORITY_READ              (1'b1                              )
			) i_dsi3_crm_data_buffer (
				.clk_rst                    (clk_rst                           ),
				.reader                     (dsi3_crm_data_readers[i].slave    ),
				.writer                     (dsi3_crm_data_writer[i]           ),
				.elip                       (elip_dsi3_crm_data_buffer[i]      ),
				.elip_registers             (elip_registers                    ),
				.o_elip_registers_data_out  (dsi3_crm_data_buffer_registers_out[i]),
				.o_data_available           (da_dsi3_crm_data[i]               ),
				.ecc_error                  (int_dsi3_crm_data_ecc_error[i].master       )
			);

			assign	dsi3_pdcm_data_buffer_full[i] = dsi3_pdcm_data_writer[i].full;
			assign	dsi3_pdcm_data_buffer_full_warn[i] = dsi3_pdcm_data_writer[i].nearly_full;
			assign	dsi3_crm_data_buffer_full[i] = dsi3_crm_data_writer[i].full;
			assign	dsi3_crm_data_buffer_full_warn[i] = dsi3_crm_data_writer[i].nearly_full;
			
			assign	dsi_cmd_buf_ecc_error.double_error[i] = int_dsi_cmd_ecc_error[i].double_error;
			assign	dsi_cmd_buf_ecc_error.single_error[i] = int_dsi_cmd_ecc_error[i].single_error;
            
			assign	dsi_crm_data_buf_ecc_error.double_error[i] = int_dsi3_crm_data_ecc_error[i].double_error;
			assign	dsi_crm_data_buf_ecc_error.single_error[i] = int_dsi3_crm_data_ecc_error[i].single_error;
			assign	dsi_pdcm_data_buf_ecc_error.double_error[i] = int_dsi3_pdcm_data_ecc_error[i].double_error;
			assign	dsi_pdcm_data_buf_ecc_error.single_error[i] = int_dsi3_pdcm_data_ecc_error[i].single_error;

		end
	endgenerate

	elip_data_t	dsi3_data_out;
	always_comb begin
		dsi3_data_out = '0;
		for (int i=0; i<DSI_CHANNELS; i++) begin
			dsi3_data_out |= dsi3_command_buffer_registers_out[i];
			dsi3_data_out |= dsi3_pdcm_data_buffer_registers_out[i];
			dsi3_data_out |= dsi3_crm_data_buffer_registers_out[i];
		end
	end
	assign	o_elip_registers_data_out = interrupt_registers_out | command_buffer_registers_out | dsi3_data_out;

	/*###   pads   ######################################################*/
	`PAD_INST(bfwb_pad, ~bfwb, bfwb, 1'b0, 1'b1, 1'b1) //TODO: use TMODE???
	`PAD_INST(dab_pad, ~dab, dab, 1'b0, 1'b1, 1'b1) //TODO: use TMODE???
	dsi_logic_t	da_dsi3_pdcm, da_dsi3_crm;

	always_ff@(posedge clk_rst.clk or negedge clk_rst.rstn) begin // pad outputs should be FFs -> no glitches
		if (clk_rst.rstn == 1'b0) begin
			dab <= 1'b1;
			da_dsi3_pdcm <= '0;
			da_dsi3_crm <= '0;
			bfwb <= 1'b1;
		end
		else begin
			dab <= dab_next;
			da_dsi3_pdcm <= da_dsi3_pdcm_data;
			da_dsi3_crm <= da_dsi3_crm_data;
			bfwb <= bfwb_next;
		end
	end

	assign	dab_next = ~((|(da_dsi3_pdcm_data))|(|(da_dsi3_crm)));
	assign	o_dsi3_pdcm_data_available = da_dsi3_pdcm;
	assign	o_dsi3_crm_data_available = da_dsi3_crm;

	assign	bfwb_next = ~(command_writer.nearly_full | (|(dsi3_command_buffer_full_warn)) | (|(dsi3_pdcm_data_buffer_full_warn)) | (|(dsi3_crm_data_buffer_full_warn)));
	assign	o_buffer_fill_warning = ~bfwb;

endmodule


