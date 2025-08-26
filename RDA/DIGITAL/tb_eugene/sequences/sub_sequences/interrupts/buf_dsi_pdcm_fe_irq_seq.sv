/*------------------------------------------------------------------------------
 * File          : buf_dsi_pdcm_fe_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class buf_dsi_pdcm_data_fe_irq_seq extends buf_base_irq_seq;
    
    `uvm_object_utils(buf_dsi_pdcm_data_fe_irq_seq) 
    
    function new(string name = "BUF.BUF_DSI_PDCM_DATA_FE");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.DSI_PDCM_FE;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_MASK.DSI_PDCM_FE;
    endfunction
    
    task apply_interrupt_condition();
        int periods = 0;
        int buffer_words = 0;
        int symbols_per_packet = 80;
        dsi3_pdcm_packet packet = new();
        tdma_scheme_pdcm scheme;
        // fill the buffer
        if(!packet.randomize() with {data.size() == symbols_per_packet; source_id_symbols == 2'd2;}) `uvm_error(this.get_name(), "randomization error")
        scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet);
        scheme.pdcm_period = 'd1000;
        `upload_tdma_scheme_with(scheme, channels == 2'b11;)
        scheme.packets[0].earliest_start_time = scheme.packets[0].earliest_start_time + 5;
        scheme.packets[0].latest_start_time = scheme.packets[0].latest_start_time - 5;
        set_tdma_scheme_pdcm(channel, scheme);
        while(buffer_words <= int'(project_pkg::SIZE_DSI_PDCM_BUF)) begin
            buffer_words += symbols_per_packet/4 + 1; // +1 word for packet status +1 frame header
            periods++;
        end
        `spi_frame_begin
        `spi_frame_create(spi_pdcm_seq, channel_bits == 2'(1 << channel); int'(pulse_count) == periods;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #((periods+1) * 1ms);
    endtask
endclass