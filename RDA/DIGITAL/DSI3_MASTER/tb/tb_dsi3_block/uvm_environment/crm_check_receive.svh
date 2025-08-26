/**
 * Class: check_transmit
 * 
 * Checker for data written into buffer received from the DSI3 slave
 */
class crm_check_receive extends check_receive#(buffer_writer_tr);
    `uvm_component_utils(crm_check_receive)
    
    protected   bit no_crm_response_expected;
    
    function new (string name = "crm_check_receive", uvm_component parent=null);
        super.new(name, parent);
        msg_type = CRM;
        no_crm_response_expected = 1'b0;
    endfunction
    
    virtual function void initialize();
        super.initialize();
        no_crm_response_expected = 1'b0;
    endfunction
    
    virtual function void expect_no_crm_response();
        no_crm_response_expected = 1'b1;
    endfunction
    
    virtual function void write_dsi3_slave(dsi3_slave_tr t); // first
        if (receiving == 1'b1) begin
            if ((t.data.size()>3)) begin
                if ((number_of_received_packets < 1)) begin
                    process_dsi3_slave_response(t);
                end
                else begin
                    `uvm_info(this.get_type_name(), $sformatf("DSI3 slave not saved:%s", t.convert2string()), UVM_HIGH)
                    fork
                        start_checking();
                    join_none
                end
            end
            else
                `uvm_info(this.get_type_name(), $sformatf("DSI3 slave not saved:%s", t.convert2string()), UVM_HIGH)
        end
        else begin
            `uvm_info(this.get_type_name(), $sformatf("DSI3 slave not saved:%s", t.convert2string()), UVM_HIGH)
        end
    endfunction
    
    virtual function void fill_buffer_queue(dsi3_slave_tr t, int packet_index = 0);
        int symbol_count;
        symbol_count = t.data.size();
        if (symbol_count >= 4) begin
            int index = 0;
            logic[15:0] data[$];
            shortint symbol_count_in_status;
            flags_container #(dsi_response_flags)   flags = new();
            int number_of_stored_words = get_number_of_stored_words(t);
            
            create_buffer_access(BUFFER_WRITE, 'h2004, index); index++; // blank header
            
            void'(convert_queue #(4, 16)::convert(t.data, data));
            begin
                symbol_count_in_status = symbol_count;
                begin
                    if (symbol_count != 8)          
                        flags.set_flags({SCE});
                    if ((t.get_begin_time() - master_start_time) < (274us+transceiver_delay-2us))
                        flags.set_flags({TE});
                    if ((t.get_begin_time() - master_start_time) > (314us+transceiver_delay))
                        flags.set_flags({TE});
                    if ((t.get_end_time() - master_start_time + (configuration.chip_time*1us) + 0.75us) > (configuration.crm_time * 1us))
                        flags.set_flags({TE});
                end
                if (t.symbol_coding_error == 1'b1)
                    flags.set_flags({SE});
                if (configuration.crc_en == 1'b1) begin
                    if (check_crc(t, msg_type) == 1'b0)
                        flags.set_flags({CRC});
                end
            end
            zero_data_not_in_symbol_count(symbol_count, data);
            for(int data_index = 0; data_index < number_of_stored_words; data_index++) begin
                create_buffer_access(BUFFER_WRITE, data[data_index], index); index++;
            end
            create_buffer_access(BUFFER_WRITE_FIRST, flags.get_values() | symbol_count_in_status, index); index++;
            create_buffer_access(BUFFER_VALIDATE, , index); index++;
        end
    endfunction
    
    virtual function int get_number_of_stored_words(dsi3_slave_tr t);
        int size = t.data.size();
        if (size[1:0] != 0)
            size = (size>>2)+1;
        else
            size = (size >> 2);
        if (t.data.size() < 4)  return 0;
        if (t.data.size() > 8)  return 2;
        return size;
    endfunction
    
    virtual function bit check_crc(dsi3_slave_tr t, dsi3_pkg::dsi3_msg_type msg_type);
        dsi3_packet packet;
        packet = dsi3_crm_packet::create_packet(t.data);
        return packet.crc_correct;
    endfunction 
    
    virtual function void add_empty_packet_when_no_response_received_in_crm();
        if (buffer_slave_transmission.size() == 0) begin
            if (number_of_received_packets == 0) begin
                if (no_crm_response_expected == 1'b0) begin
                    if (receiving == 1'b1)
                        add_empty_packet_in_buffer();
                end
            end
        end
    endfunction
    
    virtual function void compare_buffer_queues();
        add_empty_packet_when_no_response_received_in_crm();
        if (buffer_writes.size() != buffer_slave_transmission.size()) begin
            `uvm_error(this.get_type_name(), $sformatf("%p Queues do not have same sizes! Buffer writes %1d  vs. slave transmission %1d", msg_type, buffer_writes.size(), buffer_slave_transmission.size()))
            error_count++;
        end
        else begin
            while (buffer_writes.size() > 0) begin
                buffer_writer_tr    expected = buffer_writes.pop_front();
                buffer_writer_tr    slave = buffer_slave_transmission.pop_front();
                default_comparer #(.number_of_messages(10)) comparer = new();
                void'(slave.compare(expected, comparer));
            end
        end
    endfunction
    
    virtual function void create_buffer_access(buffer_writer_action_e action, int data=0, int index=0);
        buffer_writer_tr t = new($sformatf("data_buffer_write_from_slave_response_%1d", index));
        shortint ecc;
        t.action = action;
        t.data = data;
        ecc = buffer_reader_pkg::DWF_ecc_gen_chkbits(16, 6, data);
        t.ecc = ecc[5:0];
        buffer_slave_transmission.push_back(t);
    endfunction
    
    virtual function void add_empty_packet_in_buffer();
        create_buffer_access(BUFFER_WRITE, 16'h2000, 0);
        create_buffer_access(BUFFER_VALIDATE,,1);
    endfunction
    
endclass