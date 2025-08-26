-------------------------------------------------------------------------------
-- Title       : OTP WRAPPER LEVEL2
-- Project     : GED project M520.47 on TSMC/Sidense
-------------------------------------------------------------------------------
-- Description : CPU access to OTP
-------------------------------------------------------------------------------
-- Subblocks   : otpwrap_l2_cpu
-------------------------------------------------------------------------------
-- File        : otpwrap_l3_top.vhd
-- Author      : Ivonne Pera (IME) ELDO
--               Denis Poliakov (DPOL) ELSPB
-- Company     : ELMOS Semiconductor AG
-- Created     : 10.06.2016
-- Last update : 20.10.2016
-------------------------------------------------------------------------------
-- Copyright (c) 2016 ELMOS Semiconductor AG
-------------------------------------------------------------------------------
-- Revisions   :
-- Date        Version  Author  Description
-- 10.06.2016   0.1     dpol    initial release
-- 11.08.2016   0.9     dpol    a_otp_vpp, a_otp_vref added
-------------------------------------------------------------------------------
-- 21.09.2016   1.0     dpol    library WORK corrected
-- 28.09.2016   1.1     ime     deleted i_clk_sys_src, i_fosc_smt
--                              added VCC analog as input for IPS and VRR analog as output
-- 20.10.2016   1.2     dpol    a_otp_vcc commented
-------------------------------------------------------------------------------
-- IP_BUS: I_IP_BUS -> OTPWRAP_L2_CPU -> O_IP_BUS
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

library JTAG;
use JTAG.jtag_tap_pkg.t_jtag_bus;

library OTP_MEM;
use OTP_MEM.mem_pkg.t_ip_bus;
use OTP_MEM.otp_wrapper_pkg.all;

entity otpwrap_l3_top is
  port(
    -- system
    i_nrst           : in  std_logic;  -- low-active reset
    i_nrst_otpclk    : in  std_logic;  -- reset for clk23 divider
    i_clk_sys        : in  std_logic;  -- system clock
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
end otpwrap_l3_top;

architecture RTL of otpwrap_l3_top is
  -------------------------------------------------------------------------------
  -- subblocks
  -------------------------------------------------------------------------------
  component otpwrap_l2_cpu
  port (
    -- system
    i_nrst           : in  std_logic;  -- low-active reset
    i_nrst_otpclk    : in  std_logic;  -- reset for clk23 divider
    i_clk_sys        : in  std_logic;  -- system clock 1
    i_atpg_mode      : in  std_logic;  -- ATPG or IDDQ mode
    i_sleep_mode     : in  std_logic;  -- system level sleep
    i_cpu_bist       : in  std_logic;  -- CPU BIST
    
    -- ip bus interface
    i_ip_bus         : in  t_ip_bus;
    o_ip_bus         : out t_ip_bus;
    
    -- test/JTAG interface
    i_jtag_bus       : in  t_jtag_bus;
    o_jtag_bus       : out t_jtag_bus;
    o_otp_tbrq       : out std_logic; -- analog testbus request
    
    -- OTP control
    i_en_otp_prog    : in  std_logic;                     -- Hardware LOCK
    i_otp_mode       : in  std_logic_vector(1 downto 0);  -- Select Read Mode: 00 - single, 01 - differential, 10 - redundant, 11 - differential-redundant
    
    -- ANALOG
    a_otp_ehv        : in  std_logic; -- OTP analog input voltage 5V when VDD is stable
    a_otp_vbg        : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vpppad     : out std_logic; -- OTP analog output voltage for high voltage testbus
    a_otp_vref       : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vrr        : out std_logic;  -- OTP analog output voltage for testbus
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
  end component;
  -------------------------------------------------------------------------------
  
  -------------------------------------------------------------------------------
  -- signals
  -------------------------------------------------------------------------------
  
  -- CPU Key for enable OTP Programming
--signal en_otp_prog     : std_logic;
  
begin -- RTL
  
  -------------------------------------------------------------------------------
  -- subblocks instantiations
  -------------------------------------------------------------------------------
  u_otpwrap_l2_cpu: otpwrap_l2_cpu
  port map (
    -- system
    i_nrst        => i_nrst,
    i_nrst_otpclk => i_nrst_otpclk,
    i_clk_sys     => i_clk_sys,
    i_atpg_mode   => i_atpg_mode,
    i_sleep_mode  => i_sleep_mode,
    i_cpu_bist    => '0',            -- unused
    
    -- ip bus interface
    i_ip_bus      => i_ip_bus,
    o_ip_bus      => o_ip_bus,
    
    -- test/JTAG interface
    i_jtag_bus    => i_jtag_bus,
    o_jtag_bus    => o_jtag_bus,
    o_otp_tbrq    => open,
    
    -- OTP control
    i_en_otp_prog => '1',             -- TODO
    i_otp_mode    => i_read_mode,     -- not only single mode
    
    -- ANALOG
    a_otp_ehv     => a_otp_ehv,
    a_otp_vbg     => a_otp_vbg,
    a_otp_vpppad  => a_otp_vpppad,
    a_otp_vref    => a_otp_vref,
    a_otp_vrr     => a_otp_vrr,
    i_otp_write_config => i_otp_write_config
  );
  -------------------------------------------------------------------------------
end RTL;
