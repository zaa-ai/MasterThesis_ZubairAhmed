-------------------------------------------------------------------------------
-- Title       : OTP WRAPPER LEVEL1
-- Project     : standard digital IP
-------------------------------------------------------------------------------
-- Description : JTAG access to OTP
--               with multiplexor for universal CPU access
-------------------------------------------------------------------------------
-- Subblocks   : otpwrap_l0_atpg otp_ctrl
-------------------------------------------------------------------------------
-- File        : otpwrap_l1_jtag.vhd
-- Author      : Ivonne Pera (IME) ELDO
--               Denis Poliakov (DPOL) ELSPB
-- Company     : ELMOS Semiconductor AG
-- Created     : 02.06.2016
-- Last update : 17.04.2017
-------------------------------------------------------------------------------
-- Copyright (c) 2016 ELMOS Semiconductor AG
-------------------------------------------------------------------------------
-- Revisions   :
-- Date        Version  Author  Description
-- 09.06.2016   0.2     dpol    initial release
-- 08.07.2016   0.3     dpol    OE added for OTP's
-- 25.07.2016   0.5     dpol    otp_ctrl added for BIST
-- 26.07.2016   0.5.1   dpol    EN_VPP for direct JTAG corrected
--                              TBRQ connected to Active JTAG Flag
-- 01.08.2016   0.5.2   dpol    CPU HOLD corrected
-- 02.08.2016   0.5.3   dpol    en_bist removed
-- 03.08.2016   0.6     dpol    JTAG PGM 32bit 12bit data blocked
--                              Autoinc JTAG Data corrected
-- 10.08.2016   0.9     dpol    JTAG Start PGM corrected to prevent multi-start
-- 11.08.2016   1.0     dpol    OTP_RDY dummy changed to BIST signal
--                              a_otp_vpp, a_otp_vref added
-- 12.08.2016   1.0.1   dpol    Fixed synchronization for i_otp_tst for otp_ctrl
-- 15.08.2016   1.1     dpol    JTAG Access ADDR corrected for AUTO=0
-- 16.08.2016   1.2     dpol    en_latch_bist_dw added
--                              Data Latch shifted from otpwrap_l1_jtag for JTAG Direct
--                              i_cpu_otp_mode control added
-- 17.08.2016   1.3     dpol    o_sel_rd_mode, o_bist_rd_mode added
-------------------------------------------------------------------------------
-- 09.09.2016   2.0     dpol    2clock mode (10MHz/5MHz) -> 1 clock mode (24MHz)
--                              i_fosc_smt replaced by i_clk_sys
-- 19.09.2016   2.1     dpol    OTP clock 2 period for JTAG read
-- 20.09.2016   2.2     dpol    JTAG read/pgm blockage added for disabled auto mode
-- 27.09.2016   2.2     dpol    library WORK corrected
-- 28.09.2016   2.3     ime     deleted i_clk_sys_src, i_fosc_smt
--                              added VCC analog as input for IPS and VRR analog as output
--                              sensitivity list of process test_mux corrected 
-- 29.09.2016   2.4     dpol    JTAG BIST read blockage added for disabled BIST
-- 30.09.2016   2.5     dpol    Address Latch for JTAG Mode shifted to exit1_dr
-- 09.11.2016   2.6     dpol    ECC decoder connected to otp_ctrl.o_cpu_din
-- 12.11.2016   2.7     dpol    i_cpu_otpmrr_sel added
-- 14.11.2016   2.8     dpol    i_en_otp_prog as programming lock corrected
-- 18.11.2016   2.9     dpol    bypass added, ECC_ERROR added to OTP_CTRL
--                              active bypass provide latching 32bit+ECC for direct JTAG write
--                              CPU/JTAG Data Mux corrected
-- 28.11.2016   2.10    dpol    LSB/MSB register control corrected
--                              i_cpu_bistctrl_sel_lsb, i_cpu_bistctrl_sel_msb added
--                              i_cpu_bistconf_sel_lsb, i_cpu_bistconf_sel_msb added
--                              i_cpu_biststat_sel_lsb, i_cpu_biststat_sel_msb added
-------------------------------------------------------------------------------
-- 02.12.2016   2.10.1  dpol    modification of ATPG/BYPASS by Flip-Flop
-------------------------------------------------------------------------------
-- 17.04.2017   3.0     dpol    otp4kx44_cp changed to otp4kx12_cp
--                              32bit interface removed
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

library JTAG;
use JTAG.jtag_tap_pkg.t_jtag_bus;
use JTAG.jtag_tap_pkg.c_dsr_width;

library OTP_MEM;
use OTP_MEM.otp_wrapper_pkg.all;

entity otpwrap_l1_jtag is
  port(
    -- system
    i_nrst                  : in  std_logic;  -- low-active reset
    i_nrst_otpclk           : in  std_logic;  -- reset for clk_otp divider
    i_clk_sys               : in  std_logic;  -- system clock / CPU clock
    i_atpg_mode             : in  std_logic;  -- ATPG or IDDQ mode
    i_sleep_mode            : in  std_logic;  -- system level sleep
    i_cpu_bist              : in  std_logic;  -- CPU BIST mode
    o_otp_ready             : out std_logic;  -- OTP_READY for test usage
    
    -- general CPU interface
    i_en_otp_prog           : in  std_logic;                                   -- hardware lock
    i_cpu_otpsel            : in  std_logic;                                   -- cpu select OTP 12bit/32bit Array
    i_cpu_ctrlsel_lsb       : in  std_logic;                                   -- cpu select OTP Control LSB
    i_cpu_ctrlsel_msb       : in  std_logic;                                   -- cpu select OTP Control MSB
    i_cpu_bistctrl_sel_lsb  : in  std_logic;                                   -- cpu select BIST Control LSB
    i_cpu_bistctrl_sel_msb  : in  std_logic;                                   -- cpu select BIST Control MSB
    i_cpu_bistconf_sel_lsb  : in  std_logic;                                   -- cpu select BIST Config LSB
    i_cpu_bistconf_sel_msb  : in  std_logic;                                   -- cpu select BIST Config MSB
    i_cpu_biststat_sel_lsb  : in  std_logic;                                   -- cpu select BIST Status LSB
    i_cpu_biststat_sel_msb  : in  std_logic;                                   -- cpu select BIST Status MSB
    i_cpu_otpmrr_sel        : in  std_logic;                                   -- cpu select MRR Control
    i_cpu_otpmpp_sel        : in  std_logic;                                   -- cpu select MRR Control
    i_cpu_addr              : in  std_logic_vector(c_otp_wl_adr-1 downto 0);   -- cpu Address
    i_cpu_dout              : in  std_logic_vector(c_otp_wl_word-1 downto 0);  -- cpu output data for control reg and Array write / 12bit/32bit
    i_cpu_rw                : in  std_logic;                                   -- cpu read/write
    o_cpu_din               : out std_logic_vector(c_otp_wl_word-1 downto 0);  -- cpu read data from control reg or Array read / 12bit/32bit
    o_cpu_hold              : out std_logic;                                   -- cpu HOLD
    
    -- test/JTAG interface
    i_jtag_bus              : in  t_jtag_bus;
    o_jtag_bus              : out t_jtag_bus;
    o_otp_tbrq              : out std_logic; -- analog testbus requests / unused
    
    -- OTP control regs/ecc control
    i_cpu_otp_mode          : in  std_logic_vector( 1 downto 0); -- Select Read Mode: 00 - single, 01 - differential, 10 - redundant, 11 - differential-redundant
    o_sel_rd_mode           : out std_logic;                     -- Select Read Mode: "0" - CPU, "1" - BIST
    o_bist_rd_mode          : out std_logic_vector( 1 downto 0); -- Select Read Mode: 00 - single, 01 - differential, 10 - redundant, 11 - differential-redundant
    
    -- ANALOG
    a_otp_ehv               : in  std_logic; -- OTP analog input voltage 5V when VDD is stable
    a_otp_vbg               : out   std_logic; -- OTP analog output voltage for testbus
    a_otp_vpppad            : out   std_logic; -- OTP analog output voltage for high voltage testbus
    a_otp_vref              : out   std_logic; -- OTP analog output voltage for testbus
    a_otp_vrr               : out   std_logic; -- OTP analog output voltage for testbus
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
end otpwrap_l1_jtag;

architecture RTL of otpwrap_l1_jtag is
  -------------------------------------------------------------------------------
  -- subblocks
  -------------------------------------------------------------------------------
  component otpwrap_l0_atpg
  port (
    -- ATPG/BYPASS
    i_atpg_mode     : in  std_logic;  -- ATPG or IDDQ mode: array gating + input->output connected
    i_bypass_mode   : in  std_logic;  -- BYPASS mode: array gating + input->output connected
    i_nrst          : in  std_logic;  -- low-active reset
    i_clk_sys       : in  std_logic;  -- system clock / CPU clock
    
    -- OTP
    i_ctrl_otp      : in  t_cot_bus;  -- Control signals for OTP 12bit/32bit
    i_data_otp      : in  t_dot_bus;  -- Write Data for OTP 12bit/32bit
    o_data_otp      : out t_dot_bus;  -- Read Data from OTP 12bit/32bit
    
    -- Charge-Pump
    i_ctrl_cp       : in  t_ccp_bus;  -- Control signals for OTP Charge-Pump
    o_data_cp       : out t_dcp_bus;  -- Monitor signals from OTP Charge-Pump
    
    -- ANALOG
    a_otp_ehv       : in  std_logic; -- OTP analog input voltage 5V when VDD is stable
    a_otp_vbg       : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vpppad    : out std_logic; -- OTP analog output voltage for high voltage testbus
    a_otp_vref      : out std_logic; -- OTP analog output voltage for testbus
    a_otp_vrr       : out std_logic  -- OTP analog output voltage for testbus
  );
  end component;
  -------------------------------------------------------------------------------
  component otp_ctrl
  port(
    -- system interface
    i_nrst              : in  std_logic;  -- unsynchronous reset-signal
    i_clk_sys           : in  std_logic;
    i_sleep_mode        : in  std_logic;
    
    -- Interface to JTAG/CPU control
    i_otp_tst           : in  std_logic;                                  -- Active TEST interface via JTAG Interface
    i_start_otp_pgm     : in  std_logic;                                  -- Start CPU/JTAG BIST PGM
    i_start_otp_read    : in  std_logic;                                  -- Start JTAG BIST READ
    i_latch_otp_dw      : in  std_logic_vector(c_otp_wl_word-1 downto 0); -- CPU /JTAG Data for BIST PGM
    i_eccerr_l          : in  std_logic_vector(1 downto 0);               -- ECC Error Flag for OTP.DR[15:0]
    i_eccerr_h          : in  std_logic_vector(1 downto 0);               -- ECC Error Flag for OTP.DR[31:16]
    o_en_bist_rd        : out std_logic;                                  -- Enable BIST for read
    o_en_bist_pgm       : out std_logic;                                  -- Enable BIST for programming
    o_otp_rdy           : out std_logic;                                  -- Monitor Ready from BIST for Digital Monitor
    o_en_latch_bist_dw  : out std_logic;                                  -- Enable Latch Data to Write
    o_sel_rd_mode       : out std_logic;                                  -- Select Read Mode: "0" - CPU, "1" - BIST
    o_bist_rd_mode      : out std_logic_vector(1 downto 0);               -- Select Read Mode: 00 - single, 01 - differential, 10 - redundant, 11 - differential-redundant
    
    -- general CPU interface
    i_cpu_otpsel            : in  std_logic;                              -- cpu OTP Array select : write/read
    i_cpu_bistctrl_sel_lsb  : in  std_logic;                              -- cpu select BIST Control LSB
    i_cpu_bistctrl_sel_msb  : in  std_logic;                              -- cpu select BIST Control MSB
    i_cpu_bistconf_sel_lsb  : in  std_logic;                              -- cpu select BIST Config LSB
    i_cpu_bistconf_sel_msb  : in  std_logic;                              -- cpu select BIST Config MSB
    i_cpu_biststat_sel_lsb  : in  std_logic;                              -- cpu select BIST Status LSB
    i_cpu_biststat_sel_msb  : in  std_logic;                              -- cpu select BIST Status MSB
    i_cpu_otpmrr_sel        : in  std_logic;                              -- cpu select MRR Control
    i_cpu_otpmpp_sel        : in  std_logic;                              -- cpu select MRR Control
    i_cpu_rw            : in  std_logic;                                  -- cpu read/write
    i_cpu_addr          : in  std_logic_vector(c_otp_wl_adr-1 downto 0);  -- cpu Address
    i_cpu_dout          : in  std_logic_vector(c_otp_wl_word-1 downto 0); -- cpu output Data for Regs write
    o_cpu_din           : out std_logic_vector(c_otp_wl_word-1 downto 0); -- cpu read Data from Regs or OTP read
    o_cpu_otp_dr        : out std_logic_vector(c_otp_wl_word-1 downto 0); -- cpu read Data from OTP read
    o_cpu_hold          : out std_logic;                                  -- cpu HOLD
    
    -- general JTAG interface
    i_jtag_nrst         : in  std_logic;   -- 
    i_jtag_tck          : in  std_logic;   -- 
    i_update_dr_pulse   : in  std_logic;   -- on clk_sys
    i_ir_otpbist_ctrl   : in  std_logic;   -- 
    i_ir_otpbist_conf   : in  std_logic;   -- 
    i_ir_otpbist_stat   : in  std_logic;   -- 
    i_jtag_addr         : in  std_logic_vector(c_otp_wl_adr-1 downto 0);  -- JTAG Address
    i_jtag_dsr          : in  std_logic_vector(c_dsr_width-1 downto 0);
    o_jtag_dsr          : out std_logic_vector(c_dsr_width-1 downto 0);
    
    -- OTP
    o_ctrl_otp          : out t_cot_bus;   -- Control signals for OTP
    o_ctrl_cp           : out t_ccp_bus;   -- Control signals for OTP Charge-Pump
    i_data_otp          : in  t_dot_bus;   -- Read Data from OTP
    o_data_otp          : out t_dot_bus;   -- Write Data for OTP
    
    -- SFR
    i_cpu_otp_mr        : in  std_logic_vector(c_otp_wl_mr-1 downto 0);   -- MR from CPU Reg
    i_otp_mpp           : in  std_logic_vector(c_otp_wl_mpp-1 downto 0);  -- MPP from Conf Reg (IR=0x69)
    i_otp_mrr           : in  std_logic_vector(c_otp_wl_mrr-1 downto 0);  -- MRR from Conf Reg (IR=0x69)
    i_otp_mr            : in  std_logic_vector(c_otp_wl_mr-1 downto 0);   -- MR from Conf Reg (IR=0x69)
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
  end component;
  -------------------------------------------------------------------------------
  
  -------------------------------------------------------------------------------
  -- constants and types
  -------------------------------------------------------------------------------
  constant COMP_ZERO        : std_logic_vector(c_otp_wl_word-1 downto 0)               :=(others => '0');
  constant COMP_ONE         : std_logic_vector(c_otp_wl_word-1 downto 0)               :=(others => '1'); 
  
  -------------------------------------------------------------------------------
  -- signals
  -------------------------------------------------------------------------------
  -- JTAG
  signal jtag_nrst          : std_logic;
  signal jtag_tck           : std_logic;
  signal jtag_ir            : std_logic_vector(7 downto 0);
  
  signal jtag_shift_dr_fe   : std_logic;
  signal jtag_shift_dr      : std_logic;
  signal jtag_update_dr     : std_logic;
  signal jtag_capture_dr    : std_logic;
  signal jtag_update_ir_fe  : std_logic;
  signal jtag_update_ir     : std_logic;
  signal jtag_exit1_dr      : std_logic;
  signal start_read_tck     : std_logic;
  signal start_read_synch   : std_logic_vector(1 downto 0);
  signal start_read_clk     : std_logic;
  signal start_prog_tck     : std_logic;
  signal start_prog_synch   : std_logic_vector(1 downto 0);
  signal start_prog_clk     : std_logic;
  signal jtag_run_idle      : std_logic;
  signal jtag_dsr           : std_logic_vector(c_dsr_width-1 downto 0);
  signal dsr_bist2jtag      : std_logic_vector(c_dsr_width-1 downto 0);
  
  signal ir_writectrl       : std_logic; --
  signal ir_writeconf       : std_logic; -- 32bit MPP[7:0] MRR[15:0] MR[7:0]
  signal ir_otp_pgm         : std_logic; -- Write Array Data - DATA[11:0] & ADDR[11:0]
  signal ir_otp_pgm_ecc     : std_logic; -- Write CPU Data   - DATA[11:0] & ADDR[11:0], reserved for ECC
  signal ir_otp_rd          : std_logic; -- Read Array Data
  signal ir_otp_rd_ecc      : std_logic; -- Read CPU Data, reserved for ECC correction
  
  signal ir_otpbist_ctrl    : std_logic; -- BIST Control 0x6E
  signal ir_otpbist_conf    : std_logic; -- BIST Control 0x6F
  signal ir_otpbist_stat    : std_logic; -- BIST Control 0x70
  
  -- synchronization JTAG -> CLK
  signal shift_dr_synch     : std_logic_vector(2 downto 0);
  signal update_dr_pulse1   : std_logic;
  signal update_dr_pulse2   : std_logic;
  signal shift_dr_re        : std_logic;
  signal shift_dr_re_syn    : std_logic_vector(2 downto 0);
  signal update_dr_pulse_rw : std_logic;
  signal ir_prog_tck        : std_logic;
  signal ir_prog_clk        : std_logic;
  signal ir_read_tck        : std_logic;
  signal autoinc_tck        : std_logic;
  
  -----------------------------------------------------------------------------
  -- OTP Control Reg IR=0x68 (16bit)
  -----------------------------------------------------------------------------
  signal otp_tstctrl : std_logic_vector(BL_OTPCTRL-1 downto 0);
  alias en_auto      : std_logic is otp_tstctrl(BIT_EN_AUTO);    -- bit  0
  alias en_otpcp     : std_logic is otp_tstctrl(BIT_EN_OTPCP);   -- bit  1
  alias en_vpp       : std_logic is otp_tstctrl(BIT_EN_VPP);     -- bit  2
  alias en_otp       : std_logic is otp_tstctrl(BIT_EN_OTP);     -- bit  4
  alias sel_otp      : std_logic is otp_tstctrl(BIT_SEL_OTP);    -- bit  6
  alias ctrl_clk     : std_logic is otp_tstctrl(BIT_CTRL_CLK);   -- bit  8
  alias ctrl_we      : std_logic is otp_tstctrl(BIT_CTRL_WE);    -- bit  9
  alias otp_mon      : std_logic_vector (BL_OTP_MON-1 downto 0) is otp_tstctrl (BIT_OTP_MON_MSB downto BIT_OTP_MON_LSB); -- bit 10..11
  alias autoinc      : std_logic is otp_tstctrl(BIT_AUTOINC);    -- bit 12
  alias bypass       : std_logic is otp_tstctrl(BIT_BYPASS);     -- bit 13
  
  signal en_auto_clk          : std_logic; -- 
  signal otp_tst_active       : std_logic; -- '1' if one of OTP IR is active
  signal mux_tclk             : std_logic; -- multiplexed otp_clk or otp_ppclk
  signal otp_rdy              : std_logic; -- OTP BIST ready
  signal tdo_mon              : std_logic; -- signal to TDO
  signal otp_tst_active_clk   : std_logic; -- otp_tst_active / clk_sys
  
  -----------------------------------------------------------------------------
  -- OTP Config Reg JTAG IR=0x69 (32bit)
  -----------------------------------------------------------------------------
  signal otp_conf    : std_logic_vector(BL_OTP_CONF-1 downto 0);
  alias otp_mpp      : std_logic_vector(BL_OTP_MPP-1 downto 0) is otp_conf (BIT_OTP_MPP_MSB downto BIT_OTP_MPP_LSB);
  alias otp_mrr      : std_logic_vector(BL_OTP_MRR-1 downto 0) is otp_conf (BIT_OTP_MRR_MSB downto BIT_OTP_MRR_LSB);
  alias otp_mr       : std_logic_vector(BL_OTP_MR-1 downto 0) is otp_conf (BIT_OTP_MR_MSB downto BIT_OTP_MR_LSB);
  
  signal cpu_otp_mr  : std_logic_vector(BL_OTP_MR-1 downto 0);
  
  -- OTP control
  signal mux_en_otpclk   : std_logic;
  signal en_otp_vpp      : std_logic;
  signal auto_otp_sel    : std_logic;
  signal auto_otp_we     : std_logic;
  signal en_bist_rd      : std_logic;
  signal en_bist_pgm     : std_logic;
  
  signal en_latch_bist_dw: std_logic;
  signal latch_cpu_data  : std_logic;
  signal start_cpu_pgm   : std_logic;  -- Start OTP Programming : CPU
  signal start_otp_pgm   : std_logic;  -- Start OTP Programming : CPU or JTAG
  
  -- OTP data
  signal otp_din           : std_logic_vector(c_otp_wl_word-1 downto 0);
  
  signal write_data        : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal read_data_corr    : std_logic_vector(c_otp_wl_dat-1 downto 0);
  
  signal addr_tck          : std_logic_vector(c_otp_wl_adr-1 downto 0);
  signal mux_otp_addr      : std_logic_vector(c_otp_wl_adr-1 downto 0);
  
  signal bist_cpu_din      : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal bist_cpu_otp_dr   : std_logic_vector(c_otp_wl_word-1 downto 0);
  
  signal latch_otp_dw      : std_logic_vector(c_otp_wl_word-1 downto 0); -- CPU output/JTAG Data for DIRECT JTAG / BIST PGM
  
  -- clock divider
  signal en_otpclk_tck    : std_logic;
  signal en_otpclk_clk    : std_logic;
  signal en_otpimp_tck    : std_logic;
  signal en_otpimp_synch  : std_logic_vector(1 downto 0);
  signal en_otpimp_clk    : std_logic;
  signal otp_clk          : std_logic;
  signal en_otpimp_del    : std_logic;
  
  constant BL_CNT_TCLK    : integer := 6;                  -- 0..127 100MHz -> 0.78125MHz
  signal cnt_testclk      : unsigned(BL_CNT_TCLK-1 downto 0);
  constant MAX_CNT_TCLK   : unsigned(BL_CNT_TCLK-1 downto 0) := (others => '1');
  signal div_testclk      : std_logic; -- otp_clk/otp_ppclk    100MHz -> 1MHz
  
  -- OTP wrapper l0 signals
  signal ctrl_otp         : t_cot_bus;
  signal din_otp          : t_dot_bus;
  signal dout_otp         : t_dot_bus;
  signal ctrl_cp          : t_ccp_bus;
  signal data_cp          : t_dcp_bus;
  
  signal bist_ctrl_otp    : t_cot_bus;
  signal bist_din_otp     : t_dot_bus;
  signal bist_ctrl_cp     : t_ccp_bus;
  
begin -- RTL
  -------------------------------------------------------------------------------
  -- outputs control
  -------------------------------------------------------------------------------
  o_otp_tbrq     <= otp_tst_active;
  
  -------------------------------------------------------------------------------
  -- distribute signals
  -------------------------------------------------------------------------------
  o_jtag_bus.test_en       <= i_jtag_bus.test_en;
  o_jtag_bus.tck           <= i_jtag_bus.tck;
  o_jtag_bus.tdi           <= i_jtag_bus.tdi;
  o_jtag_bus.tms           <= i_jtag_bus.tms;
  o_jtag_bus.tdo_latched   <= i_jtag_bus.tdo_latched;
  o_jtag_bus.tdo_unlatched <= i_jtag_bus.tdo_unlatched or (tdo_mon and i_jtag_bus.run_idle_fe);
  o_jtag_bus.ir            <= i_jtag_bus.ir;
  o_jtag_bus.test_rst      <= i_jtag_bus.test_rst;
  o_jtag_bus.run_idle      <= i_jtag_bus.run_idle;
  o_jtag_bus.capture_dr    <= i_jtag_bus.capture_dr;
  o_jtag_bus.shift_dr      <= i_jtag_bus.shift_dr;
  o_jtag_bus.update_dr     <= i_jtag_bus.update_dr;
  o_jtag_bus.update_ir     <= i_jtag_bus.update_ir;
  o_jtag_bus.test_rst_fe   <= i_jtag_bus.test_rst_fe;
  o_jtag_bus.run_idle_fe   <= i_jtag_bus.run_idle_fe;
  o_jtag_bus.capture_dr_fe <= i_jtag_bus.capture_dr_fe;
  o_jtag_bus.shift_dr_fe   <= i_jtag_bus.shift_dr_fe;
  o_jtag_bus.update_dr_fe  <= i_jtag_bus.update_dr_fe;
  o_jtag_bus.update_ir_fe  <= i_jtag_bus.update_ir_fe;
  
  -------------------------------------------------------------------------------
  -- JTAG BUS renaming
  -------------------------------------------------------------------------------
  jtag_ir           <= i_jtag_bus.ir;
  jtag_tck          <= i_jtag_bus.tck;
  jtag_nrst         <= i_jtag_bus.test_en;
  jtag_shift_dr_fe  <= i_jtag_bus.shift_dr_fe;
  jtag_shift_dr     <= i_jtag_bus.shift_dr;
  jtag_update_dr    <= i_jtag_bus.update_dr;
  jtag_capture_dr   <= i_jtag_bus.capture_dr;
  jtag_dsr          <= i_jtag_bus.dsr;
  jtag_update_ir_fe <= i_jtag_bus.update_ir_fe;
  jtag_update_ir    <= i_jtag_bus.update_ir;
  jtag_run_idle     <= i_jtag_bus.run_idle;
  
  -------------------------------------------------------------------------------
  -- instructions resolving process
  -------------------------------------------------------------------------------
  irdec : process (jtag_ir) begin
    ir_writectrl     <= '0';
    ir_writeconf     <= '0';
    ir_otp_pgm       <= '0';
    ir_otp_pgm_ecc   <= '0';
    ir_otp_rd        <= '0';
    ir_otp_rd_ecc    <= '0';
    ir_otpbist_ctrl  <= '0';
    ir_otpbist_conf  <= '0';
    ir_otpbist_stat  <= '0';
    case (to_integer(unsigned(jtag_ir))) is
      when c_instr_otp_write_ctrl  => ir_writectrl     <= '1'; --0xa0
      when c_instr_otp_write_conf  => ir_writeconf     <= '1'; --0xa1
      when c_instr_otp_write       => ir_otp_pgm       <= '1'; --0xa2
      when c_instr_otp_read        => ir_otp_rd        <= '1'; --0xa4
      when c_instr_otpbist_ctrl    => ir_otpbist_ctrl  <= '1'; --0xa6
      when c_instr_otpbist_conf    => ir_otpbist_conf  <= '1'; --0xa7
      when c_instr_otpbist_stat    => ir_otpbist_stat  <= '1'; --0xa8
      when others                  => null;
    end case;
  end process;
  
  ir_latch_tck : process (jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      ir_prog_tck     <= '0';
      ir_read_tck     <= '0';
      jtag_exit1_dr   <= '0';
      start_prog_tck  <= '0';
      start_read_tck  <= '0';
    elsif falling_edge(jtag_tck) then
      ir_prog_tck  <= ir_otp_pgm or ir_otp_pgm_ecc;
      ir_read_tck  <= ir_otp_rd or ir_otp_rd_ecc;
      if (jtag_shift_dr = '0') and (jtag_shift_dr_fe = '1') then
        jtag_exit1_dr  <= '1';
      else
        jtag_exit1_dr  <= '0';
      end if;
      if ((ir_otp_pgm or ir_otp_pgm_ecc) = '1') and (jtag_exit1_dr = '1') then
        start_prog_tck  <= '1';
      else
        start_prog_tck  <= '0';
      end if;
      if ((ir_otp_rd or ir_otp_rd_ecc) = '1') and (jtag_exit1_dr = '1') and (en_auto = '1') then
        start_read_tck <= '1';
      else
        start_read_tck <= '0';
      end if;
    end if;
  end process;
  
  o_jtag_bus.dsr <= i_jtag_bus.dsr(c_dsr_width-1 downto c_otp_wl_word) & (i_jtag_bus.dsr(c_otp_wl_word-1 downto 0) or bist_cpu_otp_dr)  when (ir_otp_rd = '1')
  else              i_jtag_bus.dsr(c_dsr_width-1 downto c_otp_wl_dat)  & (i_jtag_bus.dsr(c_otp_wl_dat-1 downto 0)  or read_data_corr) when (ir_otp_rd_ecc = '1')
  else              i_jtag_bus.dsr(c_dsr_width-1 downto c_otp_wl_adr)  & (i_jtag_bus.dsr(c_otp_wl_adr-1 downto 0)  or addr_tck)         when (ir_otp_pgm = '1') or (ir_otp_pgm_ecc = '1')
  else              dsr_bist2jtag;
  o_jtag_bus.dsr2tdo <= i_jtag_bus.dsr2tdo or (ir_otp_rd or ir_otp_rd_ecc) or (ir_otp_pgm or ir_otp_pgm_ecc) or (ir_otpbist_ctrl or ir_otpbist_conf or ir_otpbist_stat);
  
  -------------------------------------------------------------------------------
  -- synchronization JTAG -> System clock
  -------------------------------------------------------------------------------
  shift_dr_clk : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      shift_dr_synch  <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      shift_dr_synch  <= shift_dr_synch(1 downto 0) & jtag_shift_dr_fe; -- was glitch from shift_dr
    end if;
  end process shift_dr_clk;
  update_dr_pulse1  <= '1' when (shift_dr_synch(1 downto 0) = "10") else '0';
  update_dr_pulse2  <= '1' when (shift_dr_synch(2 downto 1) = "10") else '0';
  
  shift_dr_tck : process (jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      shift_dr_re <= '0';
    elsif rising_edge(jtag_tck) then
      shift_dr_re <= jtag_shift_dr;
    end if;
  end process shift_dr_tck;
  
  shift_dr_tck_clk : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      shift_dr_re_syn   <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      shift_dr_re_syn   <= shift_dr_re_syn(1 downto 0) & shift_dr_re;
    end if;
  end process shift_dr_tck_clk;
  update_dr_pulse_rw <= '1' when (shift_dr_re_syn(2 downto 1) = "10") else '0';
  
  start_pgm_tck_clk : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      start_prog_synch   <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      start_prog_synch   <= start_prog_synch(0) & start_prog_tck;
    end if;
  end process start_pgm_tck_clk;
  
  start_prog_clk  <= '1' when (start_prog_synch(0) = '1') and (start_prog_synch(1) = '0')
  else               '0';
  
  start_read_tck_clk : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      start_read_synch   <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      start_read_synch   <= start_read_synch(0) & start_read_tck;
    end if;
  end process start_read_tck_clk;
  
  start_read_clk  <= '1' when (start_read_synch(0) = '1') and (start_read_synch(1) = '0') and (en_bist_rd = '1')
  else               '0';
  
  mode_pgm_tck_clk : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      ir_prog_clk   <= '0';
    elsif rising_edge(i_clk_sys) then
      ir_prog_clk   <= ir_prog_tck;
    end if;
  end process mode_pgm_tck_clk;
  
  -------------------------------------------------------------------------------
  -- OTP inputs control
  -------------------------------------------------------------------------------
  test_mux: process (otp_tst_active, otp_tstctrl, mux_otp_addr, ir_prog_tck, ir_read_tck,
                     en_otp_vpp, auto_otp_sel, en_bist_pgm, en_bist_rd, bist_ctrl_cp,
                     bist_ctrl_otp, bist_din_otp, auto_otp_we, otp_clk, otp_din, latch_otp_dw,
                     en_auto, en_otpcp, en_vpp, en_otp, sel_otp, ctrl_we)
  begin
    if    (otp_tst_active = '1') and (en_auto = '0') then                                -- test mode: OTP full control from JTAG.REGS (JTAG.DIRECT.FORCE)
      ctrl_cp.vrren  <= en_otpcp;
      ctrl_cp.vppen  <= en_vpp;
      ctrl_cp.mpp    <= bist_ctrl_cp.mpp;
      ctrl_cp.mrr    <= bist_ctrl_cp.mrr;
      ctrl_otp.ehv   <= en_otp;
      ctrl_otp.oe    <= en_otp;
      ctrl_otp.sel   <= sel_otp;
      ctrl_otp.we    <= ctrl_we;
      ctrl_otp.ck    <= otp_clk;
      ctrl_otp.mr    <= bist_ctrl_otp.mr;
      
      ctrl_otp.addr  <= mux_otp_addr;
      din_otp.data   <= latch_otp_dw(11 downto 0);
    elsif (otp_tst_active = '1') and (en_bist_pgm = '0') and (ir_prog_tck = '1') then    -- test mode: OTP automatic control (JTAG.DIRECT.PROG)
      ctrl_cp.vrren  <= '1';
      ctrl_cp.vppen  <= en_otp_vpp;
      ctrl_cp.mpp    <= bist_ctrl_cp.mpp;
      ctrl_cp.mrr    <= bist_ctrl_cp.mrr;
      ctrl_otp.ehv   <= '1';
      ctrl_otp.oe    <= '1';
      ctrl_otp.sel   <= auto_otp_sel;
      ctrl_otp.we    <= auto_otp_we;
      ctrl_otp.ck    <= otp_clk;
      ctrl_otp.mr    <= bist_ctrl_otp.mr;
      
      ctrl_otp.addr  <= mux_otp_addr;
      din_otp.data   <= otp_din(11 downto 0);
    elsif (otp_tst_active = '1') and (en_bist_rd = '0') and (ir_read_tck = '1') then    -- test mode: OTP automatic control (JTAG.DIRECT.READ)
      ctrl_cp.vrren  <= '1';
      ctrl_cp.vppen  <= en_otp_vpp;
      ctrl_cp.mpp    <= bist_ctrl_cp.mpp;
      ctrl_cp.mrr    <= bist_ctrl_cp.mrr;
      ctrl_otp.ehv   <= '1';
      ctrl_otp.oe    <= '1';
      ctrl_otp.sel   <= auto_otp_sel;
      ctrl_otp.we    <= auto_otp_we;
      ctrl_otp.ck    <= otp_clk;
      ctrl_otp.mr    <= bist_ctrl_otp.mr;
      
      ctrl_otp.addr  <= mux_otp_addr;
      din_otp.data   <= otp_din(11 downto 0);
    else                                                                                 -- Application mode / JTAG BIST Mode / CPU BIST Mode
      ctrl_cp        <= bist_ctrl_cp;
      ctrl_otp       <= bist_ctrl_otp;
      
      din_otp.data   <= bist_din_otp.data;
    end if;
  end process;
  
  clk_test_mux: process (otp_tst_active_clk, en_auto_clk, en_otpclk_clk, ctrl_clk) begin
    if    (otp_tst_active_clk = '1') and (en_auto_clk = '0') then  -- test mode: OTP full control from JTAG
      mux_en_otpclk   <= ctrl_clk;
    elsif (otp_tst_active_clk = '1') then                          -- test mode: OTP automatic control
      mux_en_otpclk   <= en_otpclk_clk;
    else                                                           -- application mode
      mux_en_otpclk   <= '1'; -- always enabled
    end if;
  end process;
  
  -------------------------------------------------------------------------------
  -- OTP : Address Register
  -------------------------------------------------------------------------------
  autoinc_en_tck : process (jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      autoinc_tck  <= '0';
    elsif rising_edge(jtag_tck) then
      if    (jtag_capture_dr = '1') and ((ir_otp_rd or ir_otp_rd_ecc) = '1') and (autoinc = '1') then
        autoinc_tck  <= '1';
      elsif (jtag_capture_dr = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1') and (autoinc = '1') and (en_bist_pgm = '1') then
        autoinc_tck  <= '1';
      else
        autoinc_tck  <= '0';
      end if;
    end if;
  end process;
  
  adrregproc : process(jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      addr_tck <= (others => '0');
    elsif rising_edge(jtag_tck) then
      if    (jtag_exit1_dr = '1') and (ir_otp_rd = '1') and (autoinc = '0') then
        addr_tck <= jtag_dsr(c_dsr_width-c_otp_wl_word+c_otp_wl_adr-1 downto c_dsr_width-c_otp_wl_word);
      elsif (jtag_exit1_dr = '1') and (ir_otp_rd_ecc = '1') and (autoinc = '0') then
        addr_tck <= jtag_dsr(c_dsr_width-c_otp_wl_word+c_otp_wl_adr-1 downto c_dsr_width-c_otp_wl_word);
      elsif (jtag_exit1_dr = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1') and (autoinc = '0') then
        addr_tck <= jtag_dsr(c_dsr_width-1 downto c_dsr_width-c_otp_wl_adr);
      elsif (autoinc_tck = '1') then
        addr_tck <= addr_tck + '1';
      end if;
    end if;
  end process;
  
  mux_otp_addr  <= addr_tck                                                                            when (en_auto = '0')
  else             addr_tck                                                                            when ((autoinc = '1') and ((ir_otp_rd or ir_otp_rd_ecc) = '1'))
  else             addr_tck                                                                            when ((autoinc = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1'))
  else             jtag_dsr(c_dsr_width-c_otp_wl_word+c_otp_wl_adr-1 downto c_dsr_width-c_otp_wl_word) when ((autoinc = '0') and (ir_otp_rd = '1'))
  else             jtag_dsr(c_dsr_width-c_otp_wl_word+c_otp_wl_adr-1 downto c_dsr_width-c_otp_wl_word) when ((autoinc = '0') and (ir_otp_rd_ecc = '1'))
  else             jtag_dsr(c_dsr_width-1 downto c_dsr_width-c_otp_wl_adr);
  
  -------------------------------------------------------------------------------
  -- OTP: SEL and WE automatic
  -------------------------------------------------------------------------------
  sel_we_auto_proc : process (jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      auto_otp_sel  <= '0';
      auto_otp_we   <= '0';
    elsif rising_edge(jtag_tck) then
      if (otp_tst_active = '1') and (en_auto = '0') then            -- AUTO is off
        auto_otp_sel  <= '0';
        auto_otp_we   <= '0';
      elsif (otp_tst_active = '1') and (jtag_capture_dr = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1')  then
        auto_otp_sel  <= '1';
        auto_otp_we   <= '1';
      elsif (otp_tst_active = '1') and (jtag_capture_dr = '1') and ((ir_otp_rd or ir_otp_rd_ecc) = '1')  then
        auto_otp_sel  <= '1';
        auto_otp_we   <= '0';
      elsif (otp_tst_active = '1') and (jtag_capture_dr = '1') then -- (jtag_update_dr = '1')
        auto_otp_sel  <= '0';
        auto_otp_we   <= '0';
      end if;
    end if;
  end process sel_we_auto_proc;
  
  -------------------------------------------------------------------------------
  -- OTP: Activate VPP for Programming
  -------------------------------------------------------------------------------
  en_vpp_auto_proc : process (jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      en_otp_vpp  <= '0';
    elsif rising_edge(jtag_tck) then
      if (otp_tst_active = '1') and (en_auto = '0') then            -- AUTO is off
        en_otp_vpp  <= '0';
      elsif (otp_tst_active = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1') then
        en_otp_vpp  <= '1';
      else
        en_otp_vpp  <= '0';
      end if;
    end if;
  end process en_vpp_auto_proc;
  
  -------------------------------------------------------------------------------
  -- OTP: CLOCK Control
  -------------------------------------------------------------------------------
  en_clk_auto_proc : process (jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      en_otpclk_tck  <= '0';
      en_otpimp_tck  <= '0';
    elsif rising_edge(jtag_tck) then
      if (otp_tst_active = '1') and (en_auto = '0') then            -- AUTO is off
        en_otpclk_tck  <= '0';
      elsif (otp_tst_active = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1') and (jtag_exit1_dr = '1') then   -- Rising_Edge OTP_CLK
        en_otpclk_tck  <= '1';
      elsif (otp_tst_active = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1') and (jtag_update_dr = '1') then  -- Keep 1 OTP_CLK
        en_otpclk_tck  <= '1';
      elsif (otp_tst_active = '1') and ((ir_otp_pgm or ir_otp_pgm_ecc) = '1') and (jtag_run_idle = '1') then   -- Keep old State of OTP_CLK
        en_otpclk_tck  <= en_otpclk_tck;
      elsif (otp_tst_active = '1') then
        en_otpclk_tck  <= '0';
      end if;
      
      if (otp_tst_active = '1') and (en_auto = '0') then            -- AUTO is off
        en_otpimp_tck  <= '0';
      elsif (otp_tst_active = '1') and ((ir_otp_rd or ir_otp_rd_ecc) = '1') and (jtag_exit1_dr = '1') then     -- Rising_Edge OTP_CLK
        en_otpimp_tck  <= '1';
      elsif (otp_tst_active = '1') and ((ir_otp_rd or ir_otp_rd_ecc) = '1') and (jtag_update_dr = '1') then    -- Keep 1 OTP_CLK
        en_otpimp_tck  <= '1';
      elsif (otp_tst_active = '1') and ((ir_otp_rd or ir_otp_rd_ecc) = '1') and (jtag_run_idle = '1') then     -- Keep old State of OTP_CLK
        en_otpimp_tck  <= en_otpclk_tck;
      elsif (otp_tst_active = '1') then
        en_otpimp_tck  <= '0';
      end if;
    end if;
  end process en_clk_auto_proc;
  
  en_otpclk_synch_proc : process (i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      en_otpclk_clk    <= '0';
      en_otpimp_synch  <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      en_otpclk_clk    <= en_otpclk_tck;
      en_otpimp_synch  <= en_otpimp_synch(0) & en_otpimp_tck;
    end if;
  end process en_otpclk_synch_proc;
  
  en_otpimp_clk  <= '1' when (en_otpimp_synch(1) = '0') and (en_otpimp_synch(0) = '1')
  else              '0';
  
  -------------------------------------------------------------------------------
  -- OTP: input data multiplexor
  -------------------------------------------------------------------------------
  write_data  <= i_jtag_bus.dsr(c_dsr_width-c_otp_wl_adr-1 downto c_dsr_width-c_otp_wl_adr-c_otp_wl_word) when (otp_tst_active = '1') and (ir_otp_pgm_ecc = '1') and (autoinc = '0')
  else           i_jtag_bus.dsr(c_dsr_width-1 downto c_dsr_width-c_otp_wl_word)                           when (otp_tst_active = '1') and (ir_otp_pgm_ecc = '1') and (autoinc = '1')
  else           i_cpu_dout;
  
  otp_din <= i_jtag_bus.dsr(c_dsr_width-c_otp_wl_adr-1 downto c_dsr_width-c_otp_wl_adr-c_otp_wl_word) when (otp_tst_active = '1') and (ir_otp_pgm = '1') and (autoinc = '0')
  else       i_jtag_bus.dsr(c_dsr_width-1 downto c_dsr_width-c_otp_wl_word)                           when (otp_tst_active = '1') and (ir_otp_pgm = '1') and (autoinc = '1')
  else                        write_data                                                              when (otp_tst_active = '1') and (ir_otp_pgm_ecc = '1') and (en_bist_pgm = '0') and (bypass = '0')
  else                        write_data;
  
  -------------------------------------------------------------------------------
  o_otp_ready <= otp_rdy;
  
  -------------------------------------------------------------------------------
  -- OTP: Control for BIST Start / Latch Data_Write
  -------------------------------------------------------------------------------
  start_cpu_pgm   <= '1' when (i_cpu_otpsel = '1') and (i_cpu_rw = '0') and (i_en_otp_prog = '1')
  else               '0';
  
  start_otp_pgm   <= '1' when (otp_tst_active_clk = '1') and (en_auto = '1') and (en_bist_pgm = '1') and (start_prog_clk = '1')  -- JTAG BIST Start
  else               '1' when (otp_tst_active_clk = '0') and (start_cpu_pgm = '1')                           --  CPU BIST Start
  else               '0';
  
  latch_cpu_data  <= '1' when (start_otp_pgm = '1') and (en_latch_bist_dw = '1')                         -- Latch Data_Write for BIST CPU or JTAG
  else               '1' when (en_auto = '0') and (ir_prog_clk = '1') and (update_dr_pulse_rw = '1')     -- Latch Data_Write for Force JTAG
  else               '1' when (en_bist_pgm = '0') and (ir_prog_clk = '1') and (update_dr_pulse_rw = '1') -- Latch Data_Write for Direct JTAG
  else               '0';
  
  latch_otp_input_data : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      latch_otp_dw   <= (others => '0');                     -- Data to write
    elsif rising_edge(i_clk_sys) then
      if (latch_cpu_data = '1') then
        latch_otp_dw  <= otp_din;
      end if;
    end if;
  end process latch_otp_input_data;
  
  -------------------------------------------------------------------------------
  -- OTP: CPU read output data from OTP memory or from control registers
  -------------------------------------------------------------------------------
  o_cpu_din <= bist_cpu_otp_dr(11 downto 0);
  
  -------------------------------------------------------------------------------
  -- OTP : Monitor for Testing Activation
  -------------------------------------------------------------------------------
  ctrl_otp_test : process(jtag_nrst, jtag_tck) begin
    if (jtag_nrst = '0') then
      otp_tst_active  <= '0';
    elsif falling_edge(jtag_tck) then
      if    (jtag_update_ir_fe = '1') and ((ir_writectrl or ir_writeconf or ir_otp_pgm or ir_otp_pgm_ecc or ir_otp_rd or ir_otp_rd_ecc) = '1') then
        otp_tst_active  <= '1';
      elsif (jtag_update_ir_fe = '1') and ((ir_otpbist_ctrl or ir_otpbist_conf or ir_otpbist_stat) = '1') then
        otp_tst_active  <= '1';
      elsif (jtag_update_ir_fe = '1') then
        otp_tst_active  <= '0';
      end if;
    end if;
  end process;
  
  ctrl_otp_test_clk : process(i_nrst, i_clk_sys) is begin
    if (i_nrst = '0') then
      otp_tst_active_clk  <= '1';
    elsif rising_edge(i_clk_sys) then
      otp_tst_active_clk  <= otp_tst_active;
    end if;
  end process ctrl_otp_test_clk;
  
  -------------------------------------------------------------------------------
  -- OTP : Control Register
  -------------------------------------------------------------------------------
  ctrl_otp_reg : process(jtag_nrst, jtag_tck) is begin
    if (jtag_nrst = '0') then
      en_auto      <= '1';
      en_otpcp     <= '0';
      en_vpp       <= '0';
      en_otp       <= '0';
      sel_otp      <= '0';
      ctrl_clk     <= '0';
      ctrl_we      <= '0';
      otp_mon      <= (others => '0');
      autoinc      <= '0';
      bypass       <= '0';
    elsif rising_edge(jtag_tck) then
      if (i_jtag_bus.test_rst = '1') then
        en_auto      <= '1';
        en_otpcp     <= '0';
        en_vpp       <= '0';
        en_otp       <= '0';
        sel_otp      <= '0';
        ctrl_clk     <= '0';
        ctrl_we      <= '0';
        otp_mon      <= (others => '0');
        autoinc      <= '0';
        bypass       <= '0';
      elsif ((i_jtag_bus.update_dr = '1') and (ir_writectrl = '1')) then
        en_auto      <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_EN_AUTO);
        en_otpcp     <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_EN_OTPCP);
        en_vpp       <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_EN_VPP);
        en_otp       <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_EN_OTP);
        sel_otp      <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_SEL_OTP);
        ctrl_clk     <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_CTRL_CLK);
        ctrl_we      <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_CTRL_WE);
        otp_mon      <= jtag_dsr((c_dsr_width-c_otp_wl_ctrl+BIT_OTP_MON_MSB) downto (c_dsr_width-c_otp_wl_ctrl+BIT_OTP_MON_LSB));
        autoinc      <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_AUTOINC);
        bypass       <= jtag_dsr(c_dsr_width-c_otp_wl_ctrl+BIT_BYPASS);
      end if;
    end if;
  end process ctrl_otp_reg;
  otp_tstctrl(BIT_OTP_CTRL3)   <= '0'; -- reserved
  otp_tstctrl(BIT_OTP_CTRL5)   <= '0'; -- reserved
  otp_tstctrl(BIT_OTP_CTRL7)   <= '0'; -- reserved
  otp_tstctrl(BIT_OTP_CTRL14)  <= '0'; -- reserved
  otp_tstctrl(BIT_OTP_CTRL15)  <= '0'; -- reserved
  
  en_auto_synch_clk: process(i_nrst, i_clk_sys) is begin
    if (i_nrst = '0') then
      en_auto_clk  <= '1';
    elsif rising_edge(i_clk_sys) then
      en_auto_clk  <= en_auto;
    end if;
  end process en_auto_synch_clk;
  
  -----------------------------------------------------------------------------
  -- JTAG IR=0xC2 : OTP CONFIG REGISTER
  -----------------------------------------------------------------------------
  otp_conf_reg : process(jtag_nrst, jtag_tck) is begin
    if (jtag_nrst = '0') then
		otp_mpp  <= (others => '0');
		otp_mrr(3 downto 0)               <= c_otp_vrr_dat;
		otp_mrr(c_otp_wl_mrr-1 downto 4)  <= (others => '0');
		otp_mr   <= (others => '0');
    elsif rising_edge(jtag_tck) then
      if    (i_jtag_bus.test_rst = '1') then
        otp_mpp  <= (others => '0');
        otp_mrr(3 downto 0)               <= c_otp_vrr_dat;
 		otp_mrr(c_otp_wl_mrr-1 downto 4)  <= (others => '0');
        otp_mr   <= (others => '0');
      elsif ((i_jtag_bus.update_dr = '1') and (ir_writeconf = '1')) then
        otp_mpp  <= jtag_dsr((c_dsr_width-BL_OTP_CONF+BIT_OTP_MPP_MSB) downto (c_dsr_width-BL_OTP_CONF+BIT_OTP_MPP_LSB));
        otp_mrr  <= jtag_dsr((c_dsr_width-BL_OTP_CONF+BIT_OTP_MRR_MSB) downto (c_dsr_width-BL_OTP_CONF+BIT_OTP_MRR_LSB));
        otp_mr   <= jtag_dsr((c_dsr_width-BL_OTP_CONF+BIT_OTP_MR_MSB) downto (c_dsr_width-BL_OTP_CONF+BIT_OTP_MR_LSB));
      end if;
    end if;
  end process otp_conf_reg;
  
  cpu_otp_mr  <= X"00" when (i_cpu_otp_mode = "00")
  else           X"01" when (i_cpu_otp_mode = "01")
  else           X"10" when (i_cpu_otp_mode = "10")
  else           X"11"; --  (i_cpu_otp_mode = "11")
  
  -----------------------------------------------------------------------------
  -- OTP_CLK forming
  -----------------------------------------------------------------------------
  -- # mode     function
  -- 1 toggle  application read only as ROM
  -- 2 off     remain 0 for idle state during test
  -- 3 on      remain 1 for programming 100us/300us
  -- 4 impulse test read 200ns
  -----------------------------------------------------------------------------
  -- gen clk_otp from fosc
  
  dff_otp_clk : process (i_nrst_otpclk, i_clk_sys) begin
    if (i_nrst_otpclk = '0') then
      otp_clk        <= '0';
      en_otpimp_del  <= '0';
    elsif falling_edge(i_clk_sys) then
      if (otp_tst_active_clk = '0') then        -- application mode / BIST - off
        otp_clk  <= '0';
      elsif (mux_en_otpclk = '1') then          -- test prog mode
        otp_clk  <= '1';
      elsif (en_otpimp_clk = '1') or (en_otpimp_del = '1') then          -- test read mode
        otp_clk  <= '1';
      else
        otp_clk  <= '0';
      end if;
      
      if (en_otpimp_del = '1') then
        en_otpimp_del  <= '0';
      elsif (en_otpimp_clk = '1') and (en_otpimp_del = '0') then
        en_otpimp_del  <= '1';
      end if;
    end if;
  end process dff_otp_clk;
  
  -----------------------------------------------------------------------------
  -- Digital Test Monitor for OTP
  -----------------------------------------------------------------------------
  tdo_mon  <= '0'           when (otp_mon = "00")
  else        otp_rdy       when (otp_mon = "01")
  else        div_testclk; --    (otp_mon = "10") or (otp_mon = "11")
  
  mux_tclk  <= data_cp.clkout   when (otp_tst_active = '1') and (otp_mon = "10") and (i_atpg_mode = '0')
  else         data_cp.ppclkout when (otp_tst_active = '1') and (otp_mon = "11") and (i_atpg_mode = '0')
  else         i_jtag_bus.tck;
  
  test_clk_cnt : process(jtag_nrst, mux_tclk) is begin
    if (jtag_nrst = '0') then
      cnt_testclk  <= (others => '0');
      div_testclk  <= '0';
    elsif rising_edge(mux_tclk) then
    	if ((otp_tst_active = '1') and (otp_mon(1) = '1')) then
      		cnt_testclk  <= cnt_testclk + 1;
      
      		if (cnt_testclk = MAX_CNT_TCLK) then
        		div_testclk  <= not div_testclk;
        		
      		end if;
  		end if;
    end if;
  end process test_clk_cnt;
  
  -- DUMMY
  read_data_corr(c_otp_wl_dat-1 downto 0)   <= bist_cpu_otp_dr(c_otp_wl_dat-1 downto 0);
  
  -------------------------------------------------------------------------------
  -- subblocks instantiations
  -------------------------------------------------------------------------------
  u_otpwrap_l0_atpg: otpwrap_l0_atpg
  port map (
    -- ATPG/BYPASS
    i_atpg_mode   => i_atpg_mode,
    i_bypass_mode => bypass,
    i_nrst        => i_nrst,
    i_clk_sys     => i_clk_sys,
    
    -- OTP
    i_ctrl_otp    => ctrl_otp,
    i_data_otp    => din_otp,
    o_data_otp    => dout_otp,
    
    -- Charge-Pump
    i_ctrl_cp     => ctrl_cp,
    o_data_cp     => data_cp,
    
    -- ANALOG
    a_otp_ehv     => a_otp_ehv,
    a_otp_vbg     => a_otp_vbg,
    a_otp_vpppad  => a_otp_vpppad,
    a_otp_vref    => a_otp_vref,
    a_otp_vrr     => a_otp_vrr
  );
  -------------------------------------------------------------------------------
  u_otp_ctrl: otp_ctrl
  port map (
    -- system interface
    i_nrst             => i_nrst,
    i_clk_sys          => i_clk_sys,
    i_sleep_mode       => i_sleep_mode,
    
    -- Interface to JTAG/CPU control
    i_otp_tst          => otp_tst_active_clk,
    i_start_otp_pgm    => start_otp_pgm,
    i_start_otp_read   => start_read_clk,
    i_latch_otp_dw     => latch_otp_dw,
    i_eccerr_l         => "00",
    i_eccerr_h         => "00",
    o_en_bist_rd       => en_bist_rd,
    o_en_bist_pgm      => en_bist_pgm,
    o_otp_rdy          => otp_rdy,
    o_en_latch_bist_dw => en_latch_bist_dw,
    o_sel_rd_mode      => o_sel_rd_mode,
    o_bist_rd_mode     => o_bist_rd_mode,
    
    -- general CPU interface
    i_cpu_otpsel           => i_cpu_otpsel,
    i_cpu_bistctrl_sel_lsb => i_cpu_bistctrl_sel_lsb,
    i_cpu_bistctrl_sel_msb => i_cpu_bistctrl_sel_msb,
    i_cpu_bistconf_sel_lsb => i_cpu_bistconf_sel_lsb,
    i_cpu_bistconf_sel_msb => i_cpu_bistconf_sel_msb,
    i_cpu_biststat_sel_lsb => i_cpu_biststat_sel_lsb,
    i_cpu_biststat_sel_msb => i_cpu_biststat_sel_msb,
    i_cpu_otpmrr_sel       => i_cpu_otpmrr_sel,
    i_cpu_otpmpp_sel       => i_cpu_otpmpp_sel,
    i_cpu_rw               => i_cpu_rw,
    i_cpu_addr             => i_cpu_addr,
    i_cpu_dout             => i_cpu_dout,
    o_cpu_din              => bist_cpu_din,
    o_cpu_otp_dr           => bist_cpu_otp_dr,
    o_cpu_hold             => o_cpu_hold,
    
    -- general JTAG interface
    i_jtag_nrst        => jtag_nrst,
    i_jtag_tck         => jtag_tck,
    i_update_dr_pulse  => update_dr_pulse1,
    i_ir_otpbist_ctrl  => ir_otpbist_ctrl,
    i_ir_otpbist_conf  => ir_otpbist_conf,
    i_ir_otpbist_stat  => ir_otpbist_stat,
    i_jtag_addr        => addr_tck,
    i_jtag_dsr         => jtag_dsr,
    o_jtag_dsr         => dsr_bist2jtag,
    
    -- OTP
    o_ctrl_otp         => bist_ctrl_otp,
    o_ctrl_cp          => bist_ctrl_cp,
    i_data_otp         => dout_otp,
    o_data_otp         => bist_din_otp,
    
    -- SFR
    i_cpu_otp_mr       => cpu_otp_mr,
    i_otp_mpp          => otp_mpp,
    i_otp_mrr          => otp_mrr,
    i_otp_mr           => otp_mr,
    i_otp_write_config => i_otp_write_config
  );
  -------------------------------------------------------------------------------
end RTL;
