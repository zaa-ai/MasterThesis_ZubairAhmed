top_env_config.m_dsi3_master_config[0].vif = th.dsi3_slave[0];
top_env_config.m_dsi3_master_config[1].vif = th.dsi3_slave[1];

`ifndef target_technology_FPGA
	`OTP_INST.readOtp("otp.dat");
`endif
