-------------------------------------------------------------------------------
-- Title       : OTP WRAPPER LEVEL2
-- Project     : ELDO project on TSMC/Sidense
-------------------------------------------------------------------------------
-- Description : CPU access to OTP
-------------------------------------------------------------------------------
-- Subblocks   : otpwrap_l1_jtag
-------------------------------------------------------------------------------
-- File        : otpwrap_l2_cpu.vhd
-- Author      : Ivonne Pera (IME) ELDO
--               Denis Poliakov (DPOL) ELSPB
-- Company     : ELMOS Semiconductor AG
-- Created     : 08.06.2016
-- Last update : 06.06.2017
-------------------------------------------------------------------------------
-- Copyright (c) 2016 ELMOS Semiconductor AG
-------------------------------------------------------------------------------
-- Revisions   :
-- Date        Version  Author  Description
-- 10.06.2016   0.1     dpol    initial release
-- 08.07.2016   0.2     dpol    16bit -> 8bit
-- 25.07.2016   0.5     dpol    BIST CPU Regs access added
-- 26.07.2016   0.5.1   dpol    CPU access corrected
-- 01.08.2016   0.5.2   dpol    CPU HOLD/ADDR corrected
-- 11.08.2016   0.8     dpol    a_otp_vpp, a_otp_vref added
--                              Address Link changed directly to address_map_pkg
-- 17.08.2016   0.9     dpol    i_otp_mode connected to otpwrap_l1
--                              Address Decoder Corrected
-------------------------------------------------------------------------------
-- 21.09.2016   1.0     dpol    library WORK corrected
-- 28.09.2016   1.1     ime     deleted i_clk_sys_src, i_fosc_smt
--                              added VCC analog as input for IPS and VRR analog as output
-- 11.10.2016   1.2     ime     added i_ip_bus.stb = '1' in sel signals
--                              corrected cpu_biststat_sel
--                              i_ip_bus.stb = '1' removed from final cpu_rw/en
--                              output data multiplexor corrected
-- 12.11.2016   1.3     dpol    cpu_otpmrr_sel added Address for OTP VRR
-- 15.11.2016   1.6     dpol    en_otp_prog added combined modecfg and en_otp_prog and lock_latch
-- 28.11.2016   1.7     dpol    o_ecc_error changed to bus [3:0]
-------------------------------------------------------------------------------
-- 06.06.2017   2.0     dpol    CPU access removed, 8bit <-> 32bit removed
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

library JTAG;
use JTAG.jtag_tap_pkg.t_jtag_bus;

library OTP_MEM;
use OTP_MEM.mem_pkg.c_ip_wl_adr;
use OTP_MEM.mem_pkg.t_ip_bus;
use OTP_MEM.otp_wrapper_pkg.all;

entity otpwrap_l2_cpu is
  port(
    -- system
    i_nrst           : in  std_logic;  -- low-active reset
    i_nrst_otpclk    : in  std_logic;  -- reset for clk23 divider
    i_clk_sys        : in  std_logic;  -- system clock
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
    i_otp_mode       : in  std_logic_vector( 1 downto 0); -- Select Read Mode: 00 - single, 01 - differential, 10 - redundant, 11 - differential-redundant
  --i_off_ecc        : in  std_logic;                     -- Disable ECC
  --i_decc_parity    : in  std_logic_vector(11 downto 0); -- Parity bypass for dis_ecc=1
  --o_read_parity    : out std_logic_vector(11 downto 0); -- from OTP read data bus [20:16]
  --o_ecc_error      : out std_logic_vector( 3 downto 0); -- Active ECC error: ECC_ERR[1:0] for DR[15:0], ECC_ERR[3:2] for DR[31:16]
    
    -- ANALOG
    a_otp_ehv        : in  std_logic; -- OTP analog input voltage 5V when VDD is stable
    a_otp_vbg        : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vpppad     : out std_logic; -- OTP analog output voltage for high voltage testbus
    a_otp_vref       : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vrr        : out std_logic; -- OTP analog output voltage for testbus
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
end otpwrap_l2_cpu;

architecture RTL of otpwrap_l2_cpu is
  -------------------------------------------------------------------------------
  -- subblocks
  -------------------------------------------------------------------------------
  component otpwrap_l1_jtag
  port (
    -- system
    i_nrst              : in  std_logic;  -- low-active reset
    i_nrst_otpclk       : in  std_logic;  -- reset for clk_otp divider
    i_clk_sys           : in  std_logic;  -- system clock / CPU clock
    i_atpg_mode         : in  std_logic;  -- ATPG or IDDQ mode
    i_sleep_mode        : in  std_logic;  -- system level sleep
    i_cpu_bist          : in  std_logic;  -- CPU BIST mode
    o_otp_ready         : out std_logic;
    
    -- general CPU interface
    i_en_otp_prog       : in  std_logic;                                  -- hardware lock
    i_cpu_otpsel        : in  std_logic;                                  -- cpu select OTP 44bit Array
    i_cpu_ctrlsel_lsb       : in  std_logic;                              -- cpu select OTP Control LSB
    i_cpu_ctrlsel_msb       : in  std_logic;                              -- cpu select OTP Control MSB
    i_cpu_bistctrl_sel_lsb  : in  std_logic;                              -- cpu select BIST Control LSB
    i_cpu_bistctrl_sel_msb  : in  std_logic;                              -- cpu select BIST Control MSB
    i_cpu_bistconf_sel_lsb  : in  std_logic;                              -- cpu select BIST Config LSB
    i_cpu_bistconf_sel_msb  : in  std_logic;                              -- cpu select BIST Config MSB
    i_cpu_biststat_sel_lsb  : in  std_logic;                              -- cpu select BIST Status LSB
    i_cpu_biststat_sel_msb  : in  std_logic;                              -- cpu select BIST Status MSB
    i_cpu_otpmrr_sel    : in  std_logic;                                  -- cpu select MRR Control
    i_cpu_otpmpp_sel    : in  std_logic;                                  -- cpu select MRR Control
    i_cpu_addr          : in  std_logic_vector(c_otp_wl_adr-1 downto 0);  -- cpu Address
    i_cpu_dout          : in  std_logic_vector(c_otp_wl_word-1 downto 0);  -- cpu output data for control reg and flash write / 32bit
    i_cpu_rw            : in  std_logic;                                  -- cpu read/write
    o_cpu_din           : out std_logic_vector(c_otp_wl_word-1 downto 0);  -- cpu read data from control reg or flash read / 32bit
    o_cpu_hold          : out std_logic;                                  -- cpu HOLD
    
    -- test/JTAG interface
    i_jtag_bus          : in  t_jtag_bus;
    o_jtag_bus          : out t_jtag_bus;
    o_otp_tbrq          : out std_logic; -- analog testbus requests / unused
    
    -- OTP control regs/ecc control
    i_cpu_otp_mode      : in  std_logic_vector( 1 downto 0); -- Select Read Mode: 00 - single, 01 - differential, 10 - redundant, 11 - differential-redundant
    o_sel_rd_mode       : out std_logic;                     -- Select Read Mode: "0" - CPU, "1" - BIST
    o_bist_rd_mode      : out std_logic_vector( 1 downto 0); -- Select Read Mode: 00 - single, 01 - differential, 10 - redundant, 11 - differential-redundant
    
    -- ANALOG
    a_otp_ehv           : in  std_logic; -- OTP analog input voltage 5V when VDD is stable
    a_otp_vbg           : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vpppad        : out std_logic; -- OTP analog output voltage for high voltage testbus
    a_otp_vref          : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vrr           : out std_logic; -- OTP analog output voltage for testbus
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
  end component;
  -------------------------------------------------------------------------------
  
  signal otp_ready         : std_logic;
  -------------------------------------------------------------------------------
  -- signals
  -------------------------------------------------------------------------------
  signal cpu_otpsel        : std_logic;
  signal cpu_ctrlsel       : std_logic;
  signal cpu_bistctrl_sel  : std_logic;
  signal cpu_bistconf_sel  : std_logic;
  signal cpu_biststat_sel  : std_logic;
  signal cpu_otpmrr_sel    : std_logic;
  signal cpu_otpmpp_sel    : std_logic;
  signal otp_block_ack     : std_logic;
  signal cpu_hold          : std_logic;
  
  signal cpu_ctrlsel_lsb       : std_logic;
  signal cpu_ctrlsel_msb       : std_logic;
  signal cpu_bistctrl_sel_lsb  : std_logic;
  signal cpu_bistctrl_sel_msb  : std_logic;
  signal cpu_bistconf_sel_lsb  : std_logic;  -- Read Conf
  signal cpu_bistconf_sel_msb  : std_logic;  -- Read Conf
  signal cpu_biststat_sel_lsb  : std_logic;
  signal cpu_biststat_sel_msb  : std_logic;
  signal otp_block_sel         : std_logic;
  
  signal cpu_rw           : std_logic;
  
  signal cpu_otp_sel     : std_logic;
  signal cpu_din12       : std_logic_vector(11 downto 0);
  signal cpu_dout12      : std_logic_vector(11 downto 0);
  signal cpu_addr        : std_logic_vector(c_ip_wl_adr-1 downto 0);  -- Full Address Range
  signal sys_otp_addr    : std_logic_vector(c_ip_wl_adr-1 downto 0);  -- CPU_ADDR minus OTP Start Address
  signal cpu_otp_addr    : std_logic_vector(c_otp_wl_adr-1 downto 0);
  
  signal sel_rd_mode     : std_logic;
  signal bist_rd_mode    : std_logic_vector(1 downto 0);
  signal mux_rd_mode     : std_logic_vector(1 downto 0);
  signal en_otp_prog     : std_logic;

  constant c_addr_otp_bgn           : integer := 16#0000#;
  constant c_addr_otp_end           : integer := 16#0FFF#;
  
begin -- RTL
  
  ---------------------------------------------------
  -- decode address: module selected
  ---------------------------------------------------
  cpu_otpsel            <= '1' when (i_ip_bus.stb = '1') -- and (i_ip_bus.adr >= c_addr_otp_bgn and i_ip_bus.adr <= c_addr_otp_end)
  else                     '0';
  cpu_ctrlsel_lsb       <= '0';
  cpu_ctrlsel_msb       <= '0';
  cpu_bistctrl_sel_lsb  <= '0';
  cpu_bistctrl_sel_msb  <= '0';
  cpu_bistconf_sel_lsb  <= '0';
  cpu_bistconf_sel_msb  <= '0';
  cpu_biststat_sel_lsb  <= '0';
  cpu_biststat_sel_msb  <= '0';
  cpu_otpmrr_sel        <= '0';
  cpu_otpmpp_sel        <= '0';

  cpu_ctrlsel         <= cpu_ctrlsel_lsb      or cpu_ctrlsel_msb;
  cpu_bistctrl_sel    <= cpu_bistctrl_sel_lsb or cpu_bistctrl_sel_msb;
  cpu_bistconf_sel    <= cpu_bistconf_sel_lsb or cpu_bistconf_sel_msb;
  cpu_biststat_sel    <= cpu_biststat_sel_lsb or cpu_biststat_sel_msb;
  
  otp_block_sel       <= cpu_otpsel or cpu_ctrlsel or cpu_bistctrl_sel or cpu_bistconf_sel or cpu_biststat_sel or cpu_otpmrr_sel or cpu_otpmpp_sel;
  
  ---------------------------------------------------
  -- control signals bypass
  ---------------------------------------------------
  o_ip_bus.we  <= i_ip_bus.we;
  o_ip_bus.stb <= i_ip_bus.stb;
  o_ip_bus.adr <= i_ip_bus.adr;
  o_ip_bus.sel <= i_ip_bus.sel;
  o_ip_bus.otp_ready <= otp_ready;
  -- no wait
  o_ip_bus.ack <= i_ip_bus.ack or otp_block_ack;
  
  otp_block_ack  <= cpu_ctrlsel or cpu_bistctrl_sel or cpu_bistconf_sel or cpu_biststat_sel or cpu_otpmrr_sel or cpu_otpmpp_sel
  or                (cpu_otpsel and not cpu_hold);
  
  ---------------------------------------------------
  -- write/read enable
  ---------------------------------------------------
  cpu_rw  <= not i_ip_bus.we;
  
  o_ip_bus.dat <= (i_ip_bus.dat or cpu_din12) when (otp_block_sel = '1') and (cpu_rw = '1')
  else             i_ip_bus.dat;
  
  ---------------------------------------------------
  -- Enable Programming two following conditions is True
  -- 1) system configuration mode (i_modecfg = 0)
  -- 2) OTP Programming Key is set (i_en_otp_prog = 1)
  ---------------------------------------------------
  en_otp_prog  <= '0';
  
  ---------------------------------------------------
  -- CPU write 8bit -> 32bit
  --
  -- OTP data: Hold 3 Low Bytes after Byte Write until High Byte is written
  --
  -- Control Register : only [15:0] is CPU accessible
  ---------------------------------------------------
   cpu_dout12   <= (others => '0');
  cpu_otp_sel  <= '1' when (cpu_otpsel = '1') and (cpu_rw = '1') -- read always
  else            '0';
  cpu_addr <= i_ip_bus.adr;
  
  sys_otp_addr  <= cpu_addr;
  
  mux_rd_mode  <= bist_rd_mode when (sel_rd_mode = '1')
  else            i_otp_mode;
  
  cpu_otp_addr  <= sys_otp_addr;
  
  ---------------------------------------------------
  -- CPU read 32bit -> 8bit
  ---------------------------------------------------
 
  -------------------------------------------------------------------------------
  u_otpwrap_l1_jtag: otpwrap_l1_jtag
  port map (
    -- system
    i_nrst              => i_nrst,
    i_nrst_otpclk       => i_nrst_otpclk,
    i_clk_sys           => i_clk_sys,
    i_atpg_mode         => i_atpg_mode,
    i_sleep_mode        => i_sleep_mode,
    i_cpu_bist          => i_cpu_bist,
    
    -- general CPU interface
    i_en_otp_prog           => en_otp_prog,
    i_cpu_otpsel            => cpu_otp_sel,
    i_cpu_ctrlsel_lsb       => cpu_ctrlsel_lsb,
    i_cpu_ctrlsel_msb       => cpu_ctrlsel_msb,
    i_cpu_bistctrl_sel_lsb  => cpu_bistctrl_sel_lsb,
    i_cpu_bistctrl_sel_msb  => cpu_bistctrl_sel_msb,
    i_cpu_bistconf_sel_lsb  => cpu_bistconf_sel_lsb,
    i_cpu_bistconf_sel_msb  => cpu_bistconf_sel_msb,
    i_cpu_biststat_sel_lsb  => cpu_biststat_sel_lsb,
    i_cpu_biststat_sel_msb  => cpu_biststat_sel_msb,
    i_cpu_otpmrr_sel        => cpu_otpmrr_sel,
    i_cpu_otpmpp_sel        => cpu_otpmpp_sel,
    i_cpu_addr              => cpu_otp_addr,
    i_cpu_dout              => cpu_dout12,
    i_cpu_rw                => cpu_rw,
    o_cpu_din               => cpu_din12,
    o_cpu_hold              => cpu_hold,
    
    -- test/JTAG interface
    i_jtag_bus          => i_jtag_bus,
    o_jtag_bus          => o_jtag_bus,
    o_otp_tbrq          => o_otp_tbrq,
    
    o_otp_ready         => otp_ready,
    
    -- OTP control regs/ecc control
    i_cpu_otp_mode      => mux_rd_mode,
    o_sel_rd_mode       => sel_rd_mode,
    o_bist_rd_mode      => bist_rd_mode,
    
    -- ANALOG
    a_otp_ehv           => a_otp_ehv,
    a_otp_vbg           => a_otp_vbg,
    a_otp_vpppad        => a_otp_vpppad,
    a_otp_vref          => a_otp_vref,
    a_otp_vrr           => a_otp_vrr,
    i_otp_write_config => i_otp_write_config
  );
  -------------------------------------------------------------------------------
end RTL;
