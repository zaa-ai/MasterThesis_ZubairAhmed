/*------------------------------------------------------------------------------
 * File          : spi_crc_err_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class spi_crc_err_irq_seq extends spi_base_irq_seq;
    
    `uvm_object_utils(spi_crc_err_irq_seq) 
    
    function new(string name = "SPI.CRC_ERR");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CRC_ERR;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_MASK.CRC_ERR;
    endfunction
    
    task apply_interrupt_condition();
        // send write command with CRC errors
        `spi_frame_begin
        `spi_frame_create(spi_write_master_register_seq, address == 12'(ADDR_INTERRUPT_IRQ_MASK); data == 16'h0000;)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b0;)
        `spi_frame_end
        #50us;
    endtask
endclass