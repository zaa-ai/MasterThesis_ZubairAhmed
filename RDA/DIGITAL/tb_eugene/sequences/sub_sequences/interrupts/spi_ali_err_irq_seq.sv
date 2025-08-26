/*------------------------------------------------------------------------------
 * File          : spi_ali_err_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : Jun 8, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class spi_ali_err_irq_seq extends spi_base_irq_seq;
    
    `uvm_object_utils(spi_ali_err_irq_seq) 
    
    function new(string name = "SPI.ALI_ERR");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_STAT.ALI_ERR;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_MASK.ALI_ERR; 
    endfunction
    
    task apply_interrupt_condition();
        spi_read_master_register_seq read_seq;
        `spi_frame_begin
           `spi_frame_send(read_seq, address == 12'(ADDR_DSI_0_PDCM_PERIOD);)
           read_seq.error_word_index = 1;
           read_seq.error_word_bit_count = 13;
//           `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #5us;
        `spi_frame_begin
        `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
        
        // Due to the faulty read access executed before the CMD_INC interrupt should also be set.
        registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b1);
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC.write(status, 1'b1);
        registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
    endtask
endclass