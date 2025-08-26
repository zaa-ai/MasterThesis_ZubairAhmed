/*------------------------------------------------------------------------------
 * File          : pdcm_write_frame_seq.svh
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Mar 27, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class pdcm_write_frame_seq extends pdcm_buffer_writer_default_seq;
    rand int            number_of_packets;
    rand bit            valid;
    rand bit            do_validation;
    dsi3_pdcm_packet    packets[$];
    rand logic[15:0]    frame_header;
    
    `uvm_object_utils_begin(pdcm_write_frame_seq)
        `uvm_field_int(number_of_packets, UVM_DEFAULT | UVM_DEC)
        `uvm_field_int(valid, UVM_DEFAULT | UVM_BIN)
        `uvm_field_int(do_validation, UVM_DEFAULT | UVM_BIN)
        `uvm_field_int(frame_header, UVM_DEFAULT | UVM_HEX)
    `uvm_object_utils_end
    `uvm_declare_p_sequencer(pdcm_buffer_writer_sequencer_t)
    
    /************************ Methods declarations ************************/
    function new(string name ="");
        super.new("pdcm_buffer_write_seq");
    endfunction : new
  
    /************************ User defined methods declarations ************************/
    virtual task body();
        `uvm_info(get_type_name(), "pdcm buffer write sequence starting", UVM_HIGH)
        write_data(PDCM_BUFFER_WRITE_FRAME_HEADER, $urandom());
        for (int packet_index = 0; packet_index < number_of_packets; packet_index++) begin
            packets[packet_index] = new();
            void'(packets[packet_index].randomize() with { data.size() inside {4,8,12,16,20,24,28,32,36,40,44};});
            write_packet_header();
            
            for (int data_index = 0; data_index < packets[packet_index].get_word_count(); data_index++) begin
                write_data(PDCM_BUFFER_WRITE, packets[packet_index].get_word(data_index));
            end
            write_packet_header_again(packets[packet_index]);
        end
        write_data(PDCM_BUFFER_WRITE_FRAME_HEADER_AGAIN, frame_header);
        if (do_validation == 1'b1) begin
            if (valid == 1'b1) begin
                `uvm_do_on_with(req, p_sequencer, {action == PDCM_BUFFER_VALIDATE;})
            end
            else begin
                `uvm_do_on_with(req, p_sequencer, {action == PDCM_BUFFER_INVALIDATE;})
            end
        end
        `uvm_info(get_type_name(), $sformatf("pdcm buffer write sequence completed: %s", this.convert2string()), UVM_HIGH)
    endtask
    
    task write_packet_header();
        write_data(PDCM_BUFFER_WRITE_PACKET_HEADER, $urandom());
    endtask
    
    task write_packet_header_again(dsi3_pdcm_packet packet);
        PACKET_STAT_t header;
        header = $urandom();
        header.CRC_ERR = packet.crc_correct;
        header.SYMBOL_COUNT = packet.data.size();
        write_data(PDCM_BUFFER_WRITE_PACKET_HEADER_AGAIN, header);
    endtask
    
    virtual task write_data(pdcm_buffer_writer_action_e action, shortint data);
        bit [5:0] ecc = DWF_ecc_gen_chkbits(16, 6, data);
        `uvm_do_on_with(req, p_sequencer, {action == local::action; data == local::data; ecc==local::ecc;})
    endtask
    
    function string convert2string();
        string s = super.convert2string();
        $sformat(s, {"%s\n" }, get_full_name(),);
        $sformat(s, {"packets = %1d"}, number_of_packets);
        $sformat(s, {"data = %p\naccess = WRITE\n"}, number_of_packets);
        $sformat(s, {"valid = %1b"}, valid);
        $sformat(s, {"do_validation = %1b"}, do_validation);
        return s;
    endfunction : convert2string
    
endclass