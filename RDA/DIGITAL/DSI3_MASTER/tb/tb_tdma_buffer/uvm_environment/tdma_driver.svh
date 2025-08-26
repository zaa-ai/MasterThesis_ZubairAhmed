/*------------------------------------------------------------------------------
 * File          : tdma_driver.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Feb 3, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class tdma_driver extends uvm_driver#(tdma_tr);
	
	// TODO: add class members 
	`uvm_component_utils(tdma_driver)
	
	virtual	tdma_interface vif;

	tdma_config m_config;
	
	tdma_header_t	header;
	tdma_packet_t	packet;

	
	function new (string name = "tdma_driver", uvm_component parent=null);
		super.new(name, parent);
	endfunction

	virtual task run_phase(uvm_phase phase);
		forever
			begin
				seq_item_port.get_next_item(req);
				do_drive();
				seq_item_port.item_done(rsp);
			end
	endtask : run_phase

	virtual task do_drive ();
		vif.request = 1'b1;
		vif.write = req.write;
		vif.target = req.target;
		vif.index = req.index;
		
		case (req.target)
			HEADER : begin
				vif.header_to_buffer = req.header_to_buffer;
			end
			PACKET : begin
				vif.packet_to_buffer = req.packet_to_buffer;
			end
		endcase
		@(posedge vif.acknowledge) #1;
		req.header_from_buffer = vif.header_from_buffer;
		req.packet_from_buffer = vif.packet_from_buffer;
		vif.request = 1'b0;
	endtask : do_drive
	
endclass : tdma_driver