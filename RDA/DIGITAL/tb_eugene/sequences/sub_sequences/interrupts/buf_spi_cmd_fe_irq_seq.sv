/*------------------------------------------------------------------------------
 * File          : buf_spi_cmd_fe_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class buf_spi_cmd_fe_irq_seq extends buf_base_irq_seq;
    
    `uvm_object_utils(buf_spi_cmd_fe_irq_seq) 
    
    function new(string name = "BUF.BUF_SPI_CMD_FE");
        super.new(name);
    endfunction : new
    
    constraint co_channel { channel == 0; channel_based == 1'b0;};
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.SPI_CMD_FE;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_MASK.SPI_CMD_FE;
    endfunction
    
    task apply_interrupt_condition();
        spi_read_master_register_seq read_sequences[$];
        
        `spi_frame_begin
        for (int i=0; i < int'(project_pkg::SIZE_SPI_CMD_BUF); i++) begin
            spi_read_master_register_seq read;
            `spi_frame_create(spi_pdcm_seq,)
            `spi_frame_send(read, address == 12'(addresses_pkg::ADDR_BUFFER_IRQS_BUF_FILL_WARN); burst_addresses.size() == 0;)
            read_sequences.push_back(read);
        end
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        for (int i = 0; i < read_sequences.size(); i++) begin
            int cmd_buf_warn_limit = int'($floor((project_pkg::SIZE_SPI_CMD_BUF - 16'd1) * 0.75));
            int bit_position = regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_FILL_WARN.SPI_CMD_FW.get_lsb_pos();
            bit fill_warning = read_sequences[i].data[bit_position];
            
            if(i <  cmd_buf_warn_limit && fill_warning != 1'b0) `uvm_error(this.get_name(), $sformatf("Unexpected SPI command buffer fill warning, expected 0, got 1"))
            if(i >= cmd_buf_warn_limit && fill_warning != 1'b1) `uvm_error(this.get_name(), $sformatf("Unexpected SPI command buffer fill warning, expected 1, got 0"))
        end
    endtask
endclass