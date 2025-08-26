/*------------------------------------------------------------------------------
 * File          : packet_creator.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Mar 3, 2023
 * Description   : creates packets by writing into buffer
 *------------------------------------------------------------------------------*/
class crm_packet_creator extends uvm_component;
	`uvm_component_utils(crm_packet_creator)
	
	buffer_writer_sequencer_t	sequencer;
	
	function new (string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	virtual task add_packet(spi_dsi_data_packet packet);
		buffer_write_seq buffer = new();
		shortint	header;
		header = shortint'(packet.get_values());
		header |= shortint'(packet.symbol_count);
		buffer.data.push_back(header);
		for (int i = 0; i < packet.data.size(); i++) begin
			buffer.data.push_back(packet.data[i]);
		end
		buffer.valid = 1'b1;
		buffer.do_validation = 1'b1;
		buffer.start(sequencer);
	endtask
	
endclass


class pdcm_packet_creator extends uvm_component;
    `uvm_component_utils(pdcm_packet_creator)
    
    pdcm_buffer_writer_sequencer_t   sequencer;
    
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual task add_frame(tdma_scheme_pdcm scheme, ref logic[15:0] data[$]);
        buffer_access_seq buffer = new();
        shortint    header;
        header = scheme.packets.size();
        buffer.action = PDCM_BUFFER_WRITE;
        buffer.data.push_back(header);
        data.push_back(header);
        buffer.start(sequencer);
        foreach(scheme.packets[i]) begin
            add_packet(create_packet_from_scheme(scheme.packets[i]), data);
        end
        buffer = new();
        buffer.action = PDCM_BUFFER_VALIDATE;
        buffer.start(sequencer);
    endtask
    
    virtual function spi_dsi_data_packet create_packet_from_scheme(tdma_scheme_packet tdma_packet);
        spi_dsi_data_packet spi_packet = new();
        spi_packet.set_values($random);
        spi_packet.data.delete();
        spi_packet.symbol_count = tdma_packet.symbol_count;
        for (int symbols = 0; symbols < tdma_packet.symbol_count; symbols+=4) begin
            spi_packet.data.push_back($urandom);
        end
        return spi_packet;
    endfunction
    
    virtual task add_packet(spi_dsi_data_packet packet, ref logic[15:0] data[$]);
        create_packet_header(packet, data).start(sequencer);
        create_buffer_data(packet.data, data).start(sequencer);
    endtask
    
    virtual function buffer_access_seq create_buffer_data(logic[15:0] packet_data[$], ref logic[15:0] data[$]);
        buffer_access_seq buffer = new();
        buffer.action = PDCM_BUFFER_WRITE;
        for (int i = 0; i < packet_data.size(); i++) begin
            buffer.data.push_back(packet_data[i]);
            data.push_back(packet_data[i]);
        end
        return buffer;
    endfunction
    
    virtual function buffer_access_seq create_packet_header(spi_dsi_data_packet packet, ref logic[15:0] data[$]);
        shortint    header;
        buffer_access_seq buffer = new();
        buffer.action = PDCM_BUFFER_WRITE;
        header = shortint'(packet.get_values());
        header |= shortint'(packet.symbol_count);
        buffer.data.push_back(header);
        data.push_back(header);
        return buffer;
    endfunction
    
endclass