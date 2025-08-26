/*------------------------------------------------------------------------------
 * File          : dsi_dmof_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class dsi_dmof_irq_seq extends dsi_base_irq_seq;
    
    `uvm_object_utils(dsi_dmof_irq_seq) 
    
    function new(string name = "DSI.DMOF");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_sub_irq_stat_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DMOF;
    endfunction
    
    virtual function uvm_reg_field get_sub_irq_mask_field();
        return regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_MASK.DMOF;
    endfunction
    
    task apply_interrupt_condition();
        tdma_scheme dm_scheme = tdma_scheme_dm::valid(16);
        set_tdma_scheme_dm(channel, dm_scheme);
    
        transaction_recorder.enable_recorder();     
                
        `spi_frame_begin
            `spi_frame_create(spi_discovery_mode_seq, channel_bits == (2'b01 << channel);)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #(edf_parameters.epms.t__Disc_per_8__.get_typ_time() * 16);
        #100us;
    endtask
    
    task release_interrupt_condition();
       
    endtask
endclass