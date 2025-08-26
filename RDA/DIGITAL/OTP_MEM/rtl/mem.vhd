-------------------------------------------------------------------------------
-- Title       : MEM
-- Project     : E13707 Airbag
-------------------------------------------------------------------------------
-- Description : Memory control
-------------------------------------------------------------------------------
-- Subblocks   : mem_ctrl otpwrap_l3_top
-------------------------------------------------------------------------------
-- File        : mem.vhd
-- Author      : DPOL
-- Company     : ELMOS Semiconductor AG
-- Created     : 17.04.2017
-- Last update : 14.06.2017
-------------------------------------------------------------------------------
-- Copyright (c) 2017 ELMOS Semiconductor AG
-------------------------------------------------------------------------------
-- Revisions   :
-- Date        Version  Author  Description
-- 17.04.2017   1.0     dpol    initial release
--                              interface implemented
-- 14.06.2017   1.1     dpol    o_nvm_err added
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

library OTP_MEM;
use OTP_MEM.mem_pkg.all;
use OTP_MEM.otp_wrapper_pkg.all;

library JTAG;
use JTAG.jtag_tap_pkg.t_jtag_bus;

entity mem is
  PORT (
    -- system interface
    i_sys_clk        : in  std_logic;  -- 16MHz System Clock
    i_rst_n          : in  std_logic;  -- System Reset
    i_por_n          : in  std_logic;  -- POR Reset
    i_atpg_mode      : in  std_logic;  -- ATPG : SCAN or IDDQ mode
    
    -- interface to CFG
    
    i_ip_bus         : in  t_ip_bus;
    o_ip_bus         : out t_ip_bus;
    i_sleep_mode     : in  std_logic;
    
    -- test/JTAG interface
    i_jtag_bus       : in  t_jtag_bus;
    o_jtag_bus       : out t_jtag_bus;
    
    -- ANALOG
    a_otp_ehv        : in  std_logic; -- OTP analog input  voltage 5V when VDD is stable
    a_otp_vbg        : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vpppad     : out std_logic; -- OTP analog output voltage for high voltage testbus
    a_otp_vref       : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vrr        : out std_logic; -- OTP analog output voltage for testbus
    i_read_mode		 : in  std_logic_vector(1 downto 0);
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
end mem;

architecture MEM_HIER of mem is 
  
  -------------------------------------------------------------------------------
  -- subblocks
  -------------------------------------------------------------------------------
  component otpwrap_l3_top
  port (
    -- system
    i_nrst           : in  std_logic;  -- low-active reset
    i_nrst_otpclk    : in  std_logic;  -- reset for clk23 divider
    i_clk_sys        : in  std_logic;  -- system clock 1
    i_atpg_mode      : in  std_logic;  -- ATPG : SCAN or IDDQ mode
    i_sleep_mode     : in  std_logic;  -- system level sleep
    
    -- ip bus interface
    i_ip_bus         : in  t_ip_bus;
    o_ip_bus         : out t_ip_bus;
    
    -- test/JTAG interface
    i_jtag_bus       : in  t_jtag_bus;
    o_jtag_bus       : out t_jtag_bus;
    
    -- ANALOG
    a_otp_ehv        : in  std_logic; -- OTP analog input voltage 5V when VDD is stable
    a_otp_vbg        : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vpppad     : out std_logic; -- OTP analog output voltage for high voltage testbus
    a_otp_vref       : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vrr        : out std_logic; -- OTP analog output voltage for testbus
    i_read_mode		 : in  std_logic_vector(1 downto 0);
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
  end component otpwrap_l3_top;
  -------------------------------------------------------------------------------
  
  -------------------------------------------------------------------------------
  -- constant
  -------------------------------------------------------------------------------
  
  -------------------------------------------------------------------------------
  -- signals
  -------------------------------------------------------------------------------
  
begin  -- MEM_HIER
  
  ---------------------------------------------------
  -- output mapping
  ---------------------------------------------------
  
  -------------------------------------------------------------------------------
  -- subblocks instantiations
  -------------------------------------------------------------------------------
  u_otpwrap_l3_top : otpwrap_l3_top
  port map (
    -- system
    i_nrst        => i_rst_n,
    i_nrst_otpclk => i_por_n,
    i_clk_sys     => i_sys_clk,
    i_atpg_mode   => i_atpg_mode,
    i_sleep_mode  => i_sleep_mode,
    
    -- ip bus interface
    i_ip_bus      => i_ip_bus,
    o_ip_bus      => o_ip_bus,
    
    -- test/JTAG interface
    i_jtag_bus    => i_jtag_bus,
    o_jtag_bus    => o_jtag_bus,
    
    -- ANALOG
    a_otp_ehv     => a_otp_ehv,
    a_otp_vbg     => a_otp_vbg,
    a_otp_vpppad  => a_otp_vpppad,
    a_otp_vref    => a_otp_vref,
    a_otp_vrr     => a_otp_vrr,
    i_read_mode	  => i_read_mode,
    i_otp_write_config => i_otp_write_config
  ); -- otpwrap_l3_top
  -------------------------------------------------------------------------------
end MEM_HIER; 
