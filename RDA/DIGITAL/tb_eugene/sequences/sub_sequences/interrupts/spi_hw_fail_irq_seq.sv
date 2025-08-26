/*------------------------------------------------------------------------------
 * File          : spi_hw_fail_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class spi_hw_fail_irq_seq extends spi_base_irq_seq;
    
    `uvm_object_utils(spi_hw_fail_irq_seq) 
    
    function new(string name = "SPI.HW_FAIL");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_STAT.HW_FAIL;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.SPI.SPI_registers.SPI_IRQ_MASK.HW_FAIL; 
    endfunction
    
    task apply_interrupt_condition();
        spi_read_status_seq status_seq;
        #1us;
        hdl_force(`STRING_OF(`SPI_STATE_PATH), 'hF);
        #20us;
        hdl_release(`STRING_OF(`SPI_STATE_PATH));
        #20us;
        
        `spi_frame_begin
        `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
        
        // do a read status -> see Jira Issue: P52143-394
        `spi_frame_begin
        `spi_frame_send(status_seq,)
        `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        if(status_seq.status.get_value(HE) != 1'b1) `uvm_error(this.get_type_name(), "expected HE flag in IC status word after SPI hardware fail, but no HE flag was set");
        
        // clear CRC_ERR and CMD_INC IRQs that are also set here 
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CRC_ERR.write(status, 64'b1);
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC.write(status, 64'b1);
    endtask
endclass