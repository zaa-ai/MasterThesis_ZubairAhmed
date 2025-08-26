/*------------------------------------------------------------------------------
 * File          : buf_dsi_cmd_fe_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class buf_dsi_cmd_fe_irq_seq extends buf_base_irq_seq;
    
    `uvm_object_utils(buf_dsi_cmd_fe_irq_seq) 
    
    function new(string name = "BUF.BUF_DSI_CMD_FE");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.DSI_CMD_FE;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_MASK.DSI_CMD_FE;
    endfunction
    
    task apply_interrupt_condition();
        int cmd_buf_warn_limit = int'(project_pkg::SIZE_DSI_CMD_BUF * 0.75);
        for (int i = 0; i < int'(project_pkg::SIZE_DSI_CMD_BUF); i++) begin
            logic[1:0] fill_warn = i*2 < cmd_buf_warn_limit ? 2'b00 : 2'(1 << channel); // i*2 because dsi_wait needs 2 words in command buffer
            `spi_frame_begin
            `spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'(1 << channel); wait_time == 15'd1000;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
            `spi_frame_end
            registers.check_flag(regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_FILL_WARN.DSI_CMD_FW, uvm_reg_data_t'(fill_warn));
        end
        #50us;
    endtask
    
    task release_interrupt_condition();
        `spi_frame_begin
        `spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'(1 << channel);)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        check_DSI_CMD(CMD_STATUS_READ);
    endtask
endclass