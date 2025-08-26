set_false_path -to i_pad_mux_test_csb.test_reg
set_false_path -to i_pad_mux_test_sck.test_reg
set_false_path -to i_pad_mux_test_mosi.test_reg
set_false_path -to i_pad_mux_test_miso.test_reg
set_false_path -to i_pad_mux_test_rfc.test_reg
set_false_path -to i_pad_mux_test_intb.test_reg
set_false_path -to i_pad_mux_test_syncb.test_reg
set_false_path -to i_pad_mux_test_bfwb.test_reg
set_false_path -to i_pad_mux_test_dab.test_reg
set_false_path -through i_pad_mux_test_csb.test_reg
set_false_path -through i_pad_mux_test_sck.test_reg
set_false_path -through i_pad_mux_test_mosi.test_reg
set_false_path -through i_pad_mux_test_miso.test_reg
set_false_path -through i_pad_mux_test_rfc.test_reg
set_false_path -through i_pad_mux_test_intb.test_reg
set_false_path -through i_pad_mux_test_syncb.test_reg
set_false_path -through i_pad_mux_test_bfwb.test_reg
set_false_path -through i_pad_mux_test_dab.test_reg

set_glitch_safe_data  {i_pad_mux_test__csb.test_reg   }
set_glitch_safe_data  {i_pad_mux_test__sck.test_reg   }
set_glitch_safe_data  {i_pad_mux_test__mosi.test_reg  }
set_glitch_safe_data  {i_pad_mux_test__miso.test_reg  }
set_glitch_safe_data  {i_pad_mux_test__rfc.test_reg   }
set_glitch_safe_data  {i_pad_mux_test__intb.test_reg  }
set_glitch_safe_data  {i_pad_mux_test__syncb.test_reg }
set_glitch_safe_data  {i_pad_mux_test__bfwb.test_reg  }
set_glitch_safe_data  {i_pad_mux_test__dab.test_reg   }

set_ignore_cdc_paths -name to_top -to_waveform V_CLK