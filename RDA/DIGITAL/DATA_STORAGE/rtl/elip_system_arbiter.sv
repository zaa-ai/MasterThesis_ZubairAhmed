/**
 * Module: elip_arbiter
 *
 * Module for arbiting various ELIP busses for access to RAM and registers
 */
module elip_system_arbiter import project_pkg::*;(
		clk_reset_if.slave	clk_rst,
		elip_full_if.slave	elip_write_register,
		elip_full_if.slave	elip_spi_read,
		elip_full_if.slave	elip_jtag,
		elip_full_if.slave	elip_main_fsm,
		elip_full_if.master	elip_registers,
		elip_full_if.master	elip_ram
	);

    typedef enum logic[2:0] {
    	NONE,
    	JTAG_ACCESS,
    	REGISTER_WRITE,
    	SPI_READ,
    	MAIN_FSM
    } elip_selection_t;

	elip_selection_t selector;
	elip_addr_t addr;
	data_ecc_t	data_write, data_read;
	logic		rd, wr, ready;

	/*###   selector   ######################################################*/
	always_comb begin
		selector = NONE;
		if ((elip_jtag.rd == 1'b1) || (elip_jtag.wr == 1'b1)) begin // highest prio
			selector = JTAG_ACCESS;
		end
		else begin
			if (elip_spi_read.rd == 1'b1) begin
				selector = SPI_READ;
			end
			else begin
				if ((elip_main_fsm.wr == 1'b1) || (elip_main_fsm.rd == 1'b1)) begin
					selector = MAIN_FSM;
				end
				else begin
					if (elip_write_register.wr == 1'b1)
						selector = REGISTER_WRITE;
					else
						selector = NONE;
				end
			end
		end
	end

	always_comb begin
		wr = 1'b0;
		rd = 1'b0;
		data_write = '0;
		addr = '0;
		case (selector)
			SPI_READ :  begin
				addr = elip_spi_read.addr;
				rd = elip_spi_read.rd;
			end
			JTAG_ACCESS: begin
				addr = elip_jtag.addr;
				wr = elip_jtag.wr;
				rd = elip_jtag.rd;
				data_write = elip_jtag.data_write;
			end
			REGISTER_WRITE: begin
				addr = elip_write_register.addr;
				wr = elip_write_register.wr;
				data_write = elip_write_register.data_write;
			end
			MAIN_FSM: begin
				addr = elip_main_fsm.addr;
				wr = elip_main_fsm.wr;
				data_write = elip_main_fsm.data_write;
			end
			default: begin
				wr = 1'b0;
				rd = 1'b0;
			end
		endcase
	end

	assign	elip_ram.addr = addr;
	assign	elip_registers.addr = addr;
	assign	elip_ram.data_write = data_write;
	assign	elip_registers.data_write = data_write;
	logic	access_to_ram;
	assign	access_to_ram = ((addr >= elip_addr_t'(BASE_ADDR_RAM)) && (addr < elip_addr_t'(BASE_ADDR_RAM + SIZE_RAM))) ? 1'b1 : 1'b0;

	always_comb begin
		if (access_to_ram == 1'b1) begin
			elip_ram.wr = wr;
			elip_ram.rd = rd;
			elip_registers.wr = 1'b0;
			elip_registers.rd = 1'b0;
		end
		else begin
			elip_ram.wr = 1'b0;
			elip_ram.rd = 1'b0;
			elip_registers.wr = wr;
			elip_registers.rd = rd;
		end
	end

	/*###   READY assignments   ######################################################*/
	always_comb begin
		if (access_to_ram == 1'b1)
			ready = elip_ram.ready;
		else
			ready = elip_registers.ready;
	end

	always_comb begin
		elip_jtag.ready = 1'b0;
		elip_spi_read.ready = 1'b0;
		elip_write_register.ready = 1'b0;
		elip_main_fsm.ready = 1'b0;

		case (selector)
			SPI_READ :  begin
				elip_spi_read.ready = ready;
			end
			JTAG_ACCESS: begin
				elip_jtag.ready = ready;
			end
			REGISTER_WRITE: begin
				elip_write_register.ready = ready;
			end
			MAIN_FSM: begin
				elip_main_fsm.ready = ready;
			end
		endcase
	end


	/*###   data_read assignments   ######################################################*/
	assign	elip_write_register.data_read = {data_t'(0), ECC_FOR_DATA_0};
	assign	elip_spi_read.data_read = (selector == SPI_READ) ? data_read : {data_t'(0), ECC_FOR_DATA_0};
	assign	elip_jtag.data_read = (selector == JTAG_ACCESS) ? data_read : {data_t'(0), ECC_FOR_DATA_0};
	assign	elip_main_fsm.data_read = (selector == MAIN_FSM) ? data_read : {data_t'(0), ECC_FOR_DATA_0};

	always_comb begin
		if (access_to_ram == 1'b1)
			data_read = elip_ram.data_read;
		else
			data_read = elip_registers.data_read;
	end

endmodule


