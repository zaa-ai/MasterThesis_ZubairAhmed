m_monitor.vif_clk_rst  = m_config.vif_clk_rst;
if (get_is_active() == UVM_ACTIVE)	begin
	m_driver.vif_clk_rst = m_config.vif_clk_rst;
end

