`ifndef ecc_register
`define ecc_register( _name_ , _width_ , _reset_ ) logic	_name_``_ecc_corr, _name_``_ecc_fail; \
ecc_register #( .WIDTH( _width_ ), .RESET_VAL( _reset_ )) i_``_name_``_ecc_register ( \
.clk_rst     (clk_rst    ), \
.i_waccess   (1'b1  ), \
.i_raccess   (1'b1  ), \
.i_wdata     (_name_``_next    ), \
.o_rdata     (_name_    ), \
.o_ecc_corr  (_name_``_ecc_corr ), \
.o_ecc_fail  (_name_``_ecc_fail ));
`endif
