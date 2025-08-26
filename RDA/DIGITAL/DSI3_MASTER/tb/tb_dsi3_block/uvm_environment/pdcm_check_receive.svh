/**
 * Class: check_transmit
 * 
 * Checker for data written into buffer received from the DSI3 slave
 */
class pdcm_check_receive extends check_receive#(pdcm_buffer_writer_tr);
    `uvm_component_utils(pdcm_check_receive)
    
    tdma_scheme_pdcm    scheme;
    bit pc_flag;
    int packet_index;
    
    function new (string name = "pdcm_check_receive", uvm_component parent=null);
        super.new(name, parent);
        msg_type = PDCM;
        packet_index = 0;
    endfunction
    
    virtual function void write_dsi3_master(dsi3_master_tr t);
        if (msg_type == t.msg_type) begin
            this.master_start_time = t.get_begin_time();
            this.number_of_received_packets = 0;
            receiving = 1'b1;
            transmissions.delete();
            pc_flag = 1'b0;
            packet_index = 0;
            if (defined_slave_answer == 0) create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER, 16'h0000); // initial frame header
            fork
                begin
                    #((scheme.pdcm_period - 12) * 1us - ($time() - master_start_time));
                    if (defined_slave_answer < 1) finish_frame();
                    compare_buffer_queues();
                    set_defined_slave_answer(-1);
                end
            join_none
        end
        else receiving = 1'b0;
    endfunction
    
    virtual function void finish_frame();
        shortint header = get_number_of_packets();
        header[15] = pc_flag;
        create_buffer_access(PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN, header, packet_index);
        create_buffer_access(PDCM_BUFFER_VALIDATE, 0, packet_index);
        transmissions.delete();
    endfunction
    
    virtual function void set_defined_slave_answer(int increment=1);
        if (defined_slave_answer + increment < 0) defined_slave_answer = 0;
        else    defined_slave_answer+=increment;
    endfunction
    
    virtual function void process_dsi3_slave_response(dsi3_slave_tr t);
        if (defined_slave_answer == 0) begin
            number_of_received_packets++;
            transmissions.push_back(t);
            fill_buffer_queue(t);
            `uvm_info(this.get_type_name(), $sformatf("DSI3 slave:%s", t.convert2string()), UVM_HIGH)
        end
    endfunction
    
    virtual function void set_frame(tdma_scheme scheme);
        defined_slave_answer++;
        for (int i = 0; i < scheme.packets.size; i++) begin
            tdma_scheme_packet scheme_packet = scheme.packets[i];
            dsi3_slave_tr   t = new();
            t.data = scheme_packet.packet.data;
            add_dsi3_slave_response(t);
            number_of_received_packets--;
        end
    endfunction
    
    virtual function void fill_buffer_queue(dsi3_slave_tr t, int packet_index = 0);
        int symbol_count;
        symbol_count = t.data.size();
        if ((symbol_count >= 4) || (defined_slave_answer > 0))begin
            if (scheme.packets.size >= transmissions.size) begin
                logic[15:0] data[$];
                shortint symbol_count_in_status;
                flags_container #(dsi_response_flags)   flags = new();
                flags_container #(dsi_response_flags)   empty_header_flags = new();
                int number_of_stored_words = get_number_of_stored_words(t);
                
                empty_header_flags.set_flags({SCE});
                if (symbol_count >= 4)  begin
                    if (t.symbol_coding_error == 1'b1) begin
                        for (int i = 0; i < 4; i++) begin
                            if ($isunknown(t.data[i]))
                                empty_header_flags.set_flags({SE});
                        end
                    end
                    if ((t.get_begin_time() - master_start_time) > scheme.packets[this.packet_index].latest_start_time * 1us) begin 
                        empty_header_flags.set_flags({TE});
                        flags.set_flags({TE});
                    end
                    if ((t.get_begin_time() - master_start_time) < scheme.packets[this.packet_index].earliest_start_time * 1us) begin 
                        empty_header_flags.set_flags({TE});
                        flags.set_flags({TE});
                    end
                    create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER, empty_header_flags.get_values() | 16'h0004, this.packet_index); // blank header with a symbol count of 4
                    void'(convert_queue #(4, 16)::convert(t.data, data));
                    begin
                        symbol_count_in_status = symbol_count;
                        if (symbol_count > 255) begin
                                                        flags.set_flags({SCE});
                                                        symbol_count_in_status = 16'd255;
                        end
                        if (symbol_count != scheme.packets[this.packet_index].symbol_count)
                                                        flags.set_flags({SCE});
                        if (symbol_count > 256)
                                                        symbol_count = 256;
                        if ((t.get_end_time() - master_start_time) > (scheme.pdcm_period*1us - 10us +  transceiver_delay)) 
                                                        flags.set_flags({TE});
                        if (t.symbol_coding_error == 1'b1)  flags.set_flags({SE});
                        if (configuration.crc_en == 1'b1) begin
                            if (check_crc(t, msg_type) == 1'b0)
                                                            flags.set_flags({CRC});
                        end
                    end
                    zero_data_not_in_symbol_count(symbol_count, data);
                    for(int data_index = 0; data_index < get_word_count_of_data_to_be_stored(); data_index++) begin
                        if (data_index < data.size)
                            create_buffer_access(PDCM_BUFFER_WRITE, data[data_index], this.packet_index);
                        else
                            create_buffer_access(PDCM_BUFFER_WRITE, 16'h0000, this.packet_index);
                    end
                    create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, flags.get_values() | symbol_count_in_status, this.packet_index);
                    this.packet_index++;
                end
                else                    create_buffer_access(PDCM_BUFFER_WRITE_PACKET_HEADER, 'h0000, this.packet_index); // blank header with a symbol count of 4
            end
            else
                pc_flag = 1'b1;
        end
        else void'(transmissions.pop_back());
    endfunction
    
    protected virtual function int get_word_count_of_data_to_be_stored();
        int words = scheme.packets[this.packet_index].get_word_count_of_data();
        if (words > 64) return 64;
        else return words;
    endfunction
    
    virtual function int get_number_of_stored_words(dsi3_slave_tr t);
        int size = t.data.size();
        if (size[1:0] != 0)
            size = (size>>2)+1;
        else
            size = (size >> 2);
        if (t.data.size() < 4)      return 0;
        if (t.data.size() > 255)    return 64;
        return size;
    endfunction
    
    virtual function void compare_buffer_queues();
        if (buffer_writes.size() != buffer_slave_transmission.size()) begin
            `uvm_error(this.get_type_name(), $sformatf("%p Queues do not have same sizes! Buffer writes %1d  vs. slave transmission %1d", msg_type, buffer_writes.size(), buffer_slave_transmission.size()))
            error_count++;
        end
        else begin
            while (buffer_writes.size() > 0) begin
                pdcm_buffer_writer_tr    expected = buffer_writes.pop_front();
                pdcm_buffer_writer_tr    slave = buffer_slave_transmission.pop_front();
                default_comparer #(.number_of_messages(10)) comparer = new();
                void'(slave.compare(expected, comparer));
            end
        end
    endfunction
    
    virtual function void create_buffer_access(pdcm_buffer_writer_action_e action, int data=0, int packet_index = 100);
        pdcm_buffer_writer_tr t = new($sformatf("data_buffer_write_from_slave_response_packet_%1d", packet_index));
        shortint ecc;
        t.action = action;
        t.data = data;
        ecc = buffer_reader_pkg::DWF_ecc_gen_chkbits(16, 6, data);
        t.ecc = ecc[5:0];
        buffer_slave_transmission.push_back(t);
    endfunction
    
    virtual function int get_number_of_packets();
        int packets = 0;
        foreach (transmissions[i])
            if (transmissions[i].data.size() >= 4) packets++;
        return packets;
    endfunction
    
    virtual function bit check_crc(dsi3_slave_tr t, dsi3_pkg::dsi3_msg_type msg_type);
        dsi3_packet packet;
        packet = dsi3_pdcm_packet::create_packet(t.data, scheme.packets[get_number_of_packets()-1].id_symbol_count);
        return packet.crc_correct;
    endfunction 
    
endclass
