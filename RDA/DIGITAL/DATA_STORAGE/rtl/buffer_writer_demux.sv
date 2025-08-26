/**
 * Module: buffer_writer_demux
 *
 * Demultiplexing buffer writer interfaces for PDCM and CRM
 */
module buffer_writer_demux import project_pkg::*; (
		buffer_writer_if.slave	writer,
		buffer_writer_if.master	pdcm_writer,
		buffer_writer_if.master	crm_writer,
		input	logic			is_crm
	);
	
	import buffer_if_pkg::*;
	
	assign	pdcm_writer.data = writer.data;
	assign	crm_writer.data = writer.data;
	
	always_comb begin
		case (is_crm)
			1'b0: begin
				writer.full = pdcm_writer.full;
				writer.nearly_full = pdcm_writer.nearly_full;
				writer.ready = pdcm_writer.ready;
				pdcm_writer.action = writer.action;
				crm_writer.action = IDLE_WRITE;
			end
			1'b1: begin
				writer.full = crm_writer.full;
				writer.nearly_full = crm_writer.nearly_full;
				writer.ready = crm_writer.ready;
				crm_writer.action = writer.action;
				pdcm_writer.action = IDLE_WRITE;
			end
		endcase
		
	end
	
endmodule
