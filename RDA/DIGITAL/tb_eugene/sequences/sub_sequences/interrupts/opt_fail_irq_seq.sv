/*------------------------------------------------------------------------------
 * File          : opt_fail_irq_seq.sv
 * Project       : p52144
 * Author        : jvos
 * Creation date : May 24, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

class otp_fail_irq_seq extends base_irq_check_seq;
    
    `uvm_object_utils(otp_fail_irq_seq) 
    
    function new(string name = "IRQ_STAT.OTP_FAIL");
        super.new(name);
    endfunction : new
    
    virtual task run_tests();
        get_checker_config().enable_hardware_error_check = 1'b0;
        super.run_tests();
        // restore an ECC error free OTP file
        reset_and_read_otp("otp.dat");
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual function uvm_reg_field get_irq_stat_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.OTPFAIL;
    endfunction
    
    virtual function uvm_reg_field get_irq_mask_field();
        return regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.OTPFAIL;
    endfunction
    
    task apply_interrupt_condition();
        //TODO: use otp writer! otp_addr_ecc_err contains old values -> OSC trimming register will not be written.
        reset_and_read_otp("otp_addr_ecc_err.dat");
    endtask
    
    task reset_and_read_otp(string file_name);
        read_otp(file_name);
        set_resb(0);
        #100us;
        set_resb(1);
        @(posedge rfc.D);
        #100us;
        regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.RESET.write(status, 64'b1); // clear RESET IRQ
    endtask
endclass