/*------------------------------------------------------------------------------
 * File          : spi_cmd_inc_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class spi_cmd_inc_irq_seq extends spi_base_irq_seq;
    
    `uvm_object_utils(spi_cmd_inc_irq_seq) 
    
    function new(string name = "SPI.CMD_INC");
        super.new(name);
    endfunction : new
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_MASK.CMD_INC; 
    endfunction
    
    task apply_interrupt_condition();
        // send an incomplete command
        `spi_frame_begin
 	       `spi_frame_create(spi_incomplete_read_master_register_seq, address == 12'(ADDR_DSI_0_PDCM_PERIOD); word_count == 1;)
           `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #50us;
    endtask
endclass