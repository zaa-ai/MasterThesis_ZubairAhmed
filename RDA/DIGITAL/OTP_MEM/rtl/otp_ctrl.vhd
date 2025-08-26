-------------------------------------------------------------------------------
-- Title       : OTP_CTRL
-- Project     : standard digital IP
-------------------------------------------------------------------------------
-- Description : OTP Control for CPU Read
--               BIST for Programming and Stress Testing
-------------------------------------------------------------------------------
-- Subblocks   : 
-------------------------------------------------------------------------------
-- File        : otp_ctrl.vhd
-- Author      : Ivonne Pera (IME) ELDO
--               Denis Poliakov (DPOL) ELSPB
-- Company     : ELMOS Semiconductor AG
-- Created     : 15.07.2016
-- Last update : 13.06.2017
-------------------------------------------------------------------------------
-- Copyright (c) 2016 ELMOS Semiconductor AG
-------------------------------------------------------------------------------
-- Revisions   :
-- Date        Version  Author  Description
-- 22.07.2016   0.1     dpol    initial release
-- 01.08.2016   0.2     dpol    o_cpu_hold added
-- 02.08.2016   0.3     dpol    soak corrected, i_otp_tst added
-- 08.08.2016   0.5     dpol    Read check corrected
--                              w_q_req, otp_din, otp_addr_pgm optimized for gate-count
-- 11.08.2016   0.6     dpol    o_otp_rdy added for digital monitor
-- 12.08.2016   0.7     dpol    OTP Clock fixed
-- 16.08.2016   0.8     dpol    o_en_latch_bist_dw added
--                              Data Latch shifted to otpwrap_l1_jtag for JTAG Direct
--                              i_cpu_otp_mr control added
-- 17.08.2016   0.9     dpol    o_sel_rd_mode, o_bist_rd_mode added
-- 19.08.2016   1.0     dpol    i_start_otp_read added
--                              FSM updated for BIST Read/PGM Stress
-------------------------------------------------------------------------------
-- 09.09.2016   2.0     dpol    2clock mode (10MHz/5MHz) -> 1 clock mode (24MHz)
--                              i_fosc_smt replaced by i_clk_sys
-- 20.09.2016   2.1     dpol    FSM corrected for zero read time
-- 26.09.2016   2.1.1   dpol    OTP pgm data corrected for Stress
--                              ST6_WRITE_AD1 corrected removed unused condition
-- 27.09.2016   2.1.2   ime     corrected otp_vrr
--                              deleted i_clk_sys_src, i_fosc_smt
-- 28.09.2016   2.2     dpol    bit_cnt keep last state
--                              fail1 changed to 0 for wrong programmed error
-- 24.10.2016   2.3     dpol    Address Fixing added for CPU Write/Soak
-------------------------------------------------------------------------------
-- 31.10.2016   3.0     dpol    Cache L1 added, Control Cache L0 & L1 added
--                              FSM corrected
-- 08.11.2016   3.1     dpol    FSM added new state for interrupted read
-- 11.11.2016   3.2     dpol    Cache L0&L1 Processing corrected, 
--                              FSM transition corrected
-- 12.11.2016   3.3     dpol    OTP Addr Latch corrected 
--                              FSM added new state for latching new address
--                              i_cpu_otpmrr_sel added
-- 16.11.2016   3.4     dpol    MRR[3:0] changed to CPU value during VPP_OFF state
--                              Clean WE added for IDLE state
--                              bist_ctrl register changed from 12bit to 16bit
--                              bist_ctrl.max_soak added, MAX value from 3 to 10
-- 18.11.2016   3.5     dpol    i_eccerr_l[1:0], i_eccerr_h[1:0] added
--                              CPU/JTAG Data Mux corrected
-- 28.11.2016   3.6     dpol    LSB/MSB register control corrected
--                              i_cpu_bistctrl_sel_lsb, i_cpu_bistctrl_sel_msb added
--                              i_cpu_bistconf_sel_lsb, i_cpu_bistconf_sel_msb added
--                              i_cpu_biststat_sel_lsb, i_cpu_biststat_sel_msb added
-- 15.12.2016   3.7     dpol    otp_sel synchronization added on clk_sys FE
-------------------------------------------------------------------------------
-- 07.06.2017   4.0     dpol    2Array configuration -> 1Array configuration
--                              OTP.SEL source from combinatoric/FF_FE -> FSM.STATE
-- 13.06.2017   4.0.1   dpol    Double line corrected
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_misc.all;
use ieee.numeric_std.all;

library JTAG;
use JTAG.jtag_tap_pkg.c_dsr_width;

library OTP_MEM;
use OTP_MEM.otp_wrapper_pkg.all;

entity otp_ctrl is
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
    i_cpu_otpsel            : in  std_logic;                                  -- cpu OTP Array select : write/read
    i_cpu_bistctrl_sel_lsb  : in  std_logic;                                  -- cpu select BIST Control LSB
    i_cpu_bistctrl_sel_msb  : in  std_logic;                                  -- cpu select BIST Control MSB
    i_cpu_bistconf_sel_lsb  : in  std_logic;                                  -- cpu select BIST Config LSB
    i_cpu_bistconf_sel_msb  : in  std_logic;                                  -- cpu select BIST Config MSB
    i_cpu_biststat_sel_lsb  : in  std_logic;                                  -- cpu select BIST Status LSB
    i_cpu_biststat_sel_msb  : in  std_logic;                                  -- cpu select BIST Status MSB
    i_cpu_otpmrr_sel        : in  std_logic;                                  -- cpu select MRR Control
    i_cpu_otpmpp_sel        : in  std_logic;                                  -- cpu select MRR Control
    i_cpu_rw                : in  std_logic;                                  -- cpu read/write
    i_cpu_addr              : in  std_logic_vector(c_otp_wl_adr-1 downto 0);  -- cpu Address
    i_cpu_dout              : in  std_logic_vector(c_otp_wl_word-1 downto 0); -- cpu output Data for Regs write
    o_cpu_din               : out std_logic_vector(c_otp_wl_word-1 downto 0); -- cpu read Data from Regs or OTP read
    o_cpu_otp_dr            : out std_logic_vector(c_otp_wl_word-1 downto 0); -- cpu read Data from OTP read
    o_cpu_hold              : out std_logic;                                  -- cpu HOLD
    
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
    o_ctrl_otp          : out t_cot_bus; -- Control signals for OTP
    o_ctrl_cp           : out t_ccp_bus; -- Control signals for OTP Charge-Pump
    i_data_otp          : in  t_dot_bus; -- Read Data from OTP
    o_data_otp          : out t_dot_bus; -- Write Data for OTP
    
    -- SFR
    i_cpu_otp_mr        : in  std_logic_vector(c_otp_wl_mr-1 downto 0);   -- MR from CPU Reg
    i_otp_mpp           : in  std_logic_vector(c_otp_wl_mpp-1 downto 0);  -- MPP from Conf Reg (IR=0x69)
    i_otp_mrr           : in  std_logic_vector(c_otp_wl_mrr-1 downto 0);  -- MRR from Conf Reg (IR=0x69)
    i_otp_mr            : in  std_logic_vector(c_otp_wl_mr-1 downto 0);   -- MR from Conf Reg (IR=0x69)
    i_otp_write_config  : in  std_logic_vector(BL_OTP_WRITE_CONFIG-1 downto 0)
  );
end otp_ctrl;

architecture RTL of otp_ctrl is
  -------------------------------------------------------------------------------
  -- signals
  -------------------------------------------------------------------------------
  
  -- CPU
  signal cpu_hold                : std_logic;
  signal clr_hold                : std_logic;
  
  signal cpu_otpsel              : std_logic;
  signal cpu_bistctrl_sel        : std_logic;
  signal cpu_bistctrl_sel_msb    : std_logic;
  signal cpu_bistctrl_sel_lsb    : std_logic;
  signal cpu_bistconf_sel        : std_logic;
  signal cpu_bistconf_sel_msb    : std_logic;
  signal cpu_bistconf_sel_lsb    : std_logic;
  signal cpu_biststat_sel        : std_logic;
  signal cpu_biststat_sel_msb    : std_logic;
  signal cpu_biststat_sel_lsb    : std_logic;
  signal cpu_otpmrr_sel          : std_logic;
  signal cpu_otpmpp_sel          : std_logic;
  
  -- JTAG synch
  signal ir_otpbist_ctrl_tck     : std_logic;
  signal ir_otpbist_conf_tck     : std_logic;
  signal ir_otpbist_ctrl_clk     : std_logic;
  signal ir_otpbist_conf_clk     : std_logic;
  
  -- OTP Status
  signal bist_ctrl_word      : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal bist_conf_word      : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal bist_stat_word      : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal otp_mrr_word        : std_logic_vector(c_otp_wl_word-1 downto 0);
  constant DMSB_ZEROFILL     : std_logic_vector(15 downto 0)  :=(others => '0');
  
  -- OTP Cache L0 / internal Output Register in OTP Array - Keep next CPU Address
  signal cache_l0_valid      : std_logic;
  signal cache_l0_addr       : std_logic_vector(c_otp_wl_adr-1 downto 0);
  signal rst_cache_l0        : std_logic;
  signal en_latch_cl0        : std_logic;
  
  -- OTP Cache L1 / External Register - Keep current CPU Address
  
  signal en_reload_addr      : std_logic;
  
  signal otp_addr_latch      : std_logic_vector(c_otp_wl_adr-1 downto 0);  -- Keep Address during FSM processing (prevent glitch from combinatoric)
  
  signal cpu_array_sel       : std_logic;
  signal cpu_otp_rd_sel      : std_logic;
  signal cpu_cache_l0_sel    : std_logic;
  signal reread_mux_l0       : std_logic;
  signal start_otp_read      : std_logic;
  signal en_cache_l0_read    : std_logic;
  
  signal cpu_cache_sel       : std_logic;  -- dummy
  
  -----------------------------------------------------------------------------
  -- OTP BIST Control Reg IR=0x6E (12bit)
  -----------------------------------------------------------------------------
  signal bist_ctrl   : std_logic_vector(BL_OTPBISTCTRL-1 downto 0);
  alias otp_pgm      : std_logic is bist_ctrl(BIT_OTP_PGM);
  alias otp_read     : std_logic is bist_ctrl(BIT_OTP_READ);
  alias soak         : std_logic is bist_ctrl(BIT_SOAK);
  alias en_soak      : std_logic is bist_ctrl(BIT_EN_SOAK);
  alias stress       : std_logic is bist_ctrl(BIT_STRESS);
  alias sel_trp      : std_logic is bist_ctrl(BIT_SEL_TRP);
  alias sel_rd       : std_logic is bist_ctrl(BIT_SEL_RD);
  alias sel_mpp      : std_logic is bist_ctrl(BIT_SEL_MPP);
  alias sel_mrr      : std_logic is bist_ctrl(BIT_SEL_MRR);
  alias sel_mr       : std_logic is bist_ctrl(BIT_SEL_MR);
  alias max_soak     : std_logic_vector(BL_MAX_SOAK-1 downto 0) is bist_ctrl (BIT_MAX_SOAK_MSB downto BIT_MAX_SOAK_LSB); -- bit 12..14
  
  signal stress_stat    : std_logic;
  
  constant MAX_NO_SOAK_PULSES : unsigned(BL_SOAK_PULSE-1 downto 0) := x"A";
  signal max_soak_val   : unsigned(BL_SOAK_PULSE-1 downto 0);  -- value range from 10 to 3
  
  -----------------------------------------------------------------------------
  -- OTP BIST/TEST Config Reg IR=0x6F (12bit)
  -----------------------------------------------------------------------------
  signal bist_conf   : std_logic_vector(BL_OTPBISTCONF-1 downto 0);
  alias trp          : std_logic_vector(BL_TRP-1 downto 0) is bist_conf (BIT_TRP_MSB downto BIT_TRP_LSB); -- bit 0..6
  alias bist_conf7   : std_logic is bist_conf (BIT_BIST_CONF7); -- bit  7 - unused
  alias rd_mode      : std_logic_vector(BL_RD_MODE-1 downto 0) is bist_conf (BIT_RD_MODE_MSB downto BIT_RD_MODE_LSB); -- bit 8..9
  alias eccerr_l      : std_logic_vector(BL_ECCERR_L-1 downto 0) is bist_conf (BIT_ECCERR_L_MSB downto BIT_ECCERR_L_LSB); -- bit 12..13
  alias eccerr_h      : std_logic_vector(BL_ECCERR_H-1 downto 0) is bist_conf (BIT_ECCERR_H_MSB downto BIT_ECCERR_H_LSB); -- bit 14..15
  
  constant TRP_SMALL : std_logic_vector(BL_TRP-1 downto 1) := (others => '0');
  
  -----------------------------------------------------------------------------
  -- OTP BIST Status Reg IR=0x70 (16 bit)
  -----------------------------------------------------------------------------
  signal bist_stat   : std_logic_vector(BL_OTPBISTSTAT-1 downto 0);
  alias prog_bit     : std_logic_vector(BL_PROG_BIT-1 downto 0) is bist_stat (BIT_PROG_BIT_MSB downto BIT_PROG_BIT_LSB); -- bit 0..5
  alias done         : std_logic is bist_stat (BIT_DONE);       -- bit  7
  alias soak_pulse   : std_logic_vector(BL_SOAK_PULSE-1 downto 0) is bist_stat (BIT_SOAK_PULSE_MSB downto BIT_SOAK_PULSE_LSB); -- bit 8..11
  alias busy         : std_logic is bist_stat (BIT_BUSY);       -- bit 12
  alias fail0        : std_logic is bist_stat (BIT_FAIL0);      -- bit 13
  alias fail1        : std_logic is bist_stat (BIT_FAIL1);      -- bit 14
  alias soak_stat    : std_logic is bist_stat (BIT_SOAK_STAT);  -- bit 15
  
  signal incr_soak_cnt    : std_logic;
  signal set_fail1        : std_logic;
  signal set_fail0        : std_logic;
  signal set_soak         : std_logic;
  signal clr_soak         : std_logic;
  
  -- FSM counter
  -- osc/clk_sys : 48MHz/24MHz (41.67ns)
  constant BL_WAIT_CNT    : integer :=  14; -- range= 0 .. 671us ; step= 0.04167us
  
  signal wait_cnt         : unsigned (BL_WAIT_CNT-1 downto 0); -- timer register
  signal mux_trp          : unsigned (BL_WAIT_CNT-1 downto 0); -- timer value: Based Value or Controlled by Register
  signal cnt_val          : unsigned (BL_WAIT_CNT-1 downto 0); -- Mux for value
  constant VAL_ZERO       : unsigned (BL_WAIT_CNT-1 downto 0) := (others =>'0');           -- zero
  constant VAL_OF         : unsigned (BL_WAIT_CNT-1 downto 0) := (others =>'1');           -- overflow
  constant VAL_ONE        : unsigned (BL_WAIT_CNT-1 downto 0) := (0 => '1', others =>'0'); -- one
  constant VAL_VPP_ON     : unsigned (BL_WAIT_CNT-1 downto 0) := to_unsigned( 240, BL_WAIT_CNT);--  10 us (tVPP_WARMUP + tVPPS + margin)
  constant VAL_SEL_WE     : unsigned (BL_WAIT_CNT-1 downto 0) := to_unsigned(  48, BL_WAIT_CNT);--   2 us (tSP)
  constant VAL_WRITE_CK0  : unsigned (BL_WAIT_CNT-1 downto 0) := to_unsigned(   2, BL_WAIT_CNT);--  80 ns
  constant VAL_VRR_SETUP  : unsigned (BL_WAIT_CNT-1 downto 0) := to_unsigned( 240, BL_WAIT_CNT);--  10 us (tVRR_SETUP + tVRRS + margin)
  constant VAL_READ_CK0   : unsigned (BL_WAIT_CNT-1 downto 0) := to_unsigned(   1, BL_WAIT_CNT);--  40 ns
  constant VAL_READ_CK1   : unsigned (BL_WAIT_CNT-1 downto 0) := to_unsigned(   1, BL_WAIT_CNT);--  80 ns
  
  signal VAL_WRITE_CK1 : std_logic_vector(BL_OTP_WRITE_CONFIG+2-1 downto 0);
  signal VAL_SOAK_CK1 : std_logic_vector(BL_OTP_WRITE_CONFIG+2-1 downto 0);
  
  constant ZEROFILL_TRP   : unsigned(BL_WAIT_CNT-BL_TRP-1 downto 0) := (others => '0');
  
  --
  signal flag_cnt_zero    : std_logic;
  signal flag_cnt_of      : std_logic;
  signal flag_zero_trp    : std_logic;
  signal flag_equal       : std_logic;
  signal flag_err_unprog  : std_logic;
  signal flag_bitprog_1   : std_logic;
  signal flag_cpu_rd      : std_logic;
  signal flag_jtag_rd     : std_logic;
  signal ok_addr_latch    : std_logic;
  signal en_cnt           : std_logic;
  signal en_load_cnt      : std_logic;
  
  signal flag_fsm_idle      : std_logic;
  signal flag_fsm_read      : std_logic;
  signal flag_fsm_pgm       : std_logic;

  
  -- OTP Programming BIT counter
  signal bit_cnt          : unsigned (BL_PROG_BIT-1 downto 0); -- program bit counter
  signal done_last_bit    : std_logic;
  constant MAX_BIT        : unsigned (BL_PROG_BIT-1 downto 0) := to_unsigned(11, BL_PROG_BIT); -- was 43
  constant THR_BIT        : unsigned (BL_PROG_BIT-1 downto 0) := to_unsigned(12, BL_PROG_BIT); -- was 32
  
  signal start_bit_cnt    : std_logic;
  signal incr_bit_cnt     : std_logic;
  signal done_bit_cnt     : std_logic;
  
  -- OTP 
  constant BL_OTP_ADDR    : integer := 12;
  
  signal otp_din          : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal otp_dr           : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal mux_otp_dr       : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal w_q_diff         : std_logic_vector(c_otp_wl_word-1 downto 0);
  constant OTP_DATA_ONE   : std_logic_vector(c_otp_wl_word-1 downto 0) := X"001";
  constant OTP_DATA_ZERO  : std_logic_vector(c_otp_wl_word-1 downto 0) := X"000";
  
  signal mux_otp_addr     : std_logic_vector(BL_OTP_ADDR-1 downto 0);
  
  signal en_vrr           : std_logic;
  signal en_vpp           : std_logic;
  signal otp_sel          : std_logic;
  signal otp_sel_pgm      : std_logic;
  signal otp_sel_rd       : std_logic;
  signal otp_we           : std_logic;
  signal otp_ck           : std_logic;
  signal otp_oe           : std_logic;
  
  signal en_shft_data     : std_logic;
  signal latch_cpu_data   : std_logic;
  signal latch_diff_data  : std_logic;
  signal en_clr_data      : std_logic;
  
  signal set_vrr_en       : std_logic;
  signal clr_vrr_en       : std_logic;
  signal set_otp_vpp      : std_logic;
  signal set_otp_sel      : std_logic;
  signal set_otp_sel_rd   : std_logic;
  signal set_otp_we       : std_logic;
  signal set_otp_ck       : std_logic;
  signal set_otp_oe       : std_logic;
  signal clr_otp_vpp      : std_logic;
  signal clr_otp_sel      : std_logic;
  signal clr_otp_sel_rd   : std_logic;
  signal clr_otp_we       : std_logic;
  signal clr_otp_ck       : std_logic;
  signal clr_otp_oe       : std_logic;
  signal clr_stat         : std_logic;
  signal en_latch_dr      : std_logic;
  signal clr_busy         : std_logic;
  
  -- OTP : VRR config
  signal sel_otp_vrr      : std_logic_vector(1 downto 0);                     -- b00 - VRR0, b01 - VRR1, b10/11 - VRR2
  signal en_sel_otp_vrr   : std_logic;
  
  constant BL_OTP_VRR     : integer :=  2;
  signal otp_vrr_mode     : std_logic_vector(BL_OTP_VRR-1 downto 0);
  
  constant BL_VRR_CONF    : integer :=  4;
  constant VAL_VRR0       : std_logic_vector(BL_VRR_CONF-1 downto 0) := "0100";
  constant VAL_VRR1       : std_logic_vector(BL_VRR_CONF-1 downto 0) := "1000";
  constant VAL_VRR2       : std_logic_vector(BL_VRR_CONF-1 downto 0) := "1111";
  signal otp_vrr          : std_logic_vector(BL_VRR_CONF-1 downto 0);
  
  constant BL_OTP_MRR     : integer := 16;
  constant BL_OTP_MR      : integer :=  8;
  constant BL_OTP_MPP     : integer :=  8;
  signal otp_mrr          : std_logic_vector(BL_OTP_MRR-1 downto 0);
  signal otp_mr           : std_logic_vector(BL_OTP_MR-1 downto 0);
  signal otp_mpp          : std_logic_vector(BL_OTP_MPP-1 downto 0);
  
  -- SOAK
  signal sel_read2        : std_logic;
  signal set_read2        : std_logic;
  signal clr_read2        : std_logic;
  signal soak_cnt         : unsigned(BL_SOAK_PULSE-1 downto 0);
  
  --
  signal cpu_mpp          : std_logic_vector(c_otp_wl_mpp-1 downto 0);
  signal cpu_mrr          : std_logic_vector(c_otp_wl_mrr-1 downto 0);
  
  -------------------------------------------------------------------------------
  -- FSM
  -------------------------------------------------------------------------------
 type otp_ctrl_state is (
    ST0_SLEEP,         --  1   reset/sleep/standby
    ST1_IDLE,          --  2   idle state/ wait for cpu_read /cpu_prog/jtag_prog
    ST20_SEL_READ,     --  21  select OTP read / set WE SEL
    ST2_CPU_CK1,       --  3   read OTP / high phase clock
    ST17_CPU_CK0,      --  18  read OTP / low phase clock
    ST3_VPP_ON,        --  4   pause: 10us for VPP start-up
    ST4_WRITE_VRR,     --  5   pause: 10us for VRR new value
    ST5_WRITE_SEL_WE,  --  6   OTP: SEL WE
    ST6_WRITE_AD1,     --  7   OTP: ADDR DW
    ST7_WRITE_AD2,     --  8   OTP: CK high
    ST8_WRITE_CK1,     --  9   pause: wait for 100us/400us OTP: CK=0
    ST9_WRITE_CK0,     -- 10   pause: for CK down
    ST10_READ_VRR,     -- 11   pause: 10us for VRR new value
    ST11_READ_A,       -- 12   OTP: Address
    ST12_READ_CK1,     -- 13   OTP: CLK high phase read
    ST13_READ_CK0,     -- 14   OTP: CLK low phase read
    ST14_READ_EVAL,    -- 15   check: data check
    ST15_FINISH,       -- 16   finish: release signals
    ST16_VPP_OFF       -- 17   finish: VPP shut-down
  );
  signal SYS_STATE   : otp_ctrl_state;
  signal NEXT_STATE  : otp_ctrl_state;
  
begin -- RTL
  
  -------------------------------------------------------------------------------
  -- output
  -------------------------------------------------------------------------------
  o_ctrl_otp.ck    <= otp_ck;
  o_ctrl_cp.vrren  <= en_vrr;
  o_ctrl_cp.vppen  <= en_vpp;
  o_ctrl_otp.we    <= otp_we;
  o_ctrl_otp.ehv   <= en_vrr;
  o_ctrl_otp.oe    <= otp_oe;
  o_ctrl_otp.sel   <= otp_sel;
  o_ctrl_otp.mr    <= otp_mr;
  o_ctrl_cp.mrr    <= otp_mrr;
  o_ctrl_cp.mpp    <= otp_mpp;
  o_ctrl_otp.addr  <= mux_otp_addr;
  o_data_otp.data  <= otp_din;
  
  o_jtag_dsr <= i_jtag_dsr(c_dsr_width-1 downto BL_OTPBISTCTRL) & (i_jtag_dsr(BL_OTPBISTCTRL-1 downto 0) or bist_ctrl) when (i_ir_otpbist_ctrl = '1')
  else          i_jtag_dsr(c_dsr_width-1 downto BL_OTPBISTCONF) & (i_jtag_dsr(BL_OTPBISTCONF-1 downto 0) or bist_conf) when (i_ir_otpbist_conf = '1')
  else          i_jtag_dsr(c_dsr_width-1 downto BL_OTPBISTSTAT) & (i_jtag_dsr(BL_OTPBISTSTAT-1 downto 0) or bist_stat) when (i_ir_otpbist_stat = '1')
  else          i_jtag_dsr(c_dsr_width-1 downto 0);
  
  o_en_bist_rd        <= not otp_read;
  o_en_bist_pgm       <= not otp_pgm;
  
  o_en_latch_bist_dw  <= '1' when (SYS_STATE = ST1_IDLE)
  else                   '0';
  
  o_sel_rd_mode       <= sel_rd;
  o_bist_rd_mode      <= rd_mode;
  
  -------------------------------------------------------------------------------
  -- input
  -------------------------------------------------------------------------------
  otp_dr  <= i_data_otp.data;
  mux_otp_dr  <= otp_dr;
  
  cpu_otpsel        <= '0' when (i_otp_tst = '1')
  else                 i_cpu_otpsel;
  cpu_bistctrl_sel  	<= '0';
  cpu_bistctrl_sel_lsb  <= '0';
  cpu_bistctrl_sel_msb  <= '0';
  cpu_bistconf_sel  	<= '0';
  cpu_bistconf_sel_lsb  <= '0';
  cpu_bistconf_sel_msb  <= '0';
  cpu_biststat_sel  	<= '0';
  cpu_biststat_sel_lsb  <= '0';
  cpu_biststat_sel_msb  <= '0';
  cpu_otpmrr_sel    <= '0';
  cpu_otpmpp_sel	<= '0';
  -------------------------------------------------------------------------------
  -- OTP: CPU read output data from OTP Array or from test registers
  -------------------------------------------------------------------------------
  o_cpu_din <= x"000";
  
  o_cpu_otp_dr  <= mux_otp_dr;
  
  bist_ctrl_word  <= X"000";
  bist_conf_word  <= X"000";
  bist_stat_word  <= X"000";
  otp_mrr_word    <= X"000";
  
  o_cpu_hold  <= cpu_hold or i_otp_tst;
  
  o_otp_rdy  <= not busy;
  
  
  VAL_WRITE_CK1 <= "00" & i_otp_write_config;
  VAL_SOAK_CK1 <= i_otp_write_config & "00";
  
  -------------------------------------------------------------------------------
  -- JTAG -> CLK_SYS
  -------------------------------------------------------------------------------
  ir_latch_tck : process (i_jtag_nrst, i_jtag_tck) begin
    if (i_jtag_nrst = '0') then
      ir_otpbist_ctrl_tck    <= '0';
      ir_otpbist_conf_tck    <= '0';
    elsif falling_edge(i_jtag_tck) then
      ir_otpbist_ctrl_tck    <= i_ir_otpbist_ctrl;
      ir_otpbist_conf_tck    <= i_ir_otpbist_conf;
    end if;
  end process;
  
  ir_latch_clk : process (i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      ir_otpbist_ctrl_clk    <= '0';
      ir_otpbist_conf_clk    <= '0';
    elsif rising_edge(i_clk_sys) then
      ir_otpbist_ctrl_clk    <= ir_otpbist_ctrl_tck;
      ir_otpbist_conf_clk    <= ir_otpbist_conf_tck;
    end if;
  end process;
  
  -------------------------------------------------------------------------------
  -- CPU HOLD Generation
  -------------------------------------------------------------------------------
  cpu_hold_ctrl : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      cpu_hold  <= '1';
    elsif falling_edge(i_clk_sys) then
      if (clr_hold = '1') then
        cpu_hold  <= '0';
      else
        cpu_hold  <= '1';
      end if;
    end if;
  end process cpu_hold_ctrl;
  
  -------------------------------------------------------------------------------
  -- OTP Cache L0
  -------------------------------------------------------------------------------
  cache_l0_ctrl : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      cache_l0_valid  <= '0';
      cache_l0_addr   <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if    (rst_cache_l0 = '1') then
        cache_l0_valid  <= '0';
      elsif (en_latch_cl0 = '1') then
        cache_l0_valid  <= '1';
        cache_l0_addr   <= otp_addr_latch;
      elsif (i_start_otp_pgm = '1') then
        cache_l0_valid  <= '0';
        cache_l0_addr   <= i_cpu_addr;           -- cache Address used to keep CPU Program/Soak Address
      end if;
    end if;
  end process cache_l0_ctrl;
  
  cpu_cache_sel  <= '1' when (cache_l0_valid = '1') and (cache_l0_addr = i_cpu_addr)
  else              '0';
  
  -------------------------------------------------------------------------------
  -- OTP Cache L0 Monitor
  -------------------------------------------------------------------------------
  -- #  Mode         Actions
  -- 1  SysReset     Sleep -> Idle
  -- 2  Idle         Wait First CPU Read, to Fix initial Address (A0)
  -- 3  Init         CPU - Hold 3clk, Read OTP Address A0 (4clk), OTP.DR -> L0(A0 D3-0) & L1(A0 D3-0) the same
  -- 4  L0.Update    Due same Address L0.Am=L1.Am, Read OTP Address Am+1 (4clk), OTP.DR -> L0(Am+1), L1(Am)
    -------------------------------------------------------------------------------
  flag_cpu_rd       <= '1' when ((cpu_otpsel = '1') and (i_cpu_rw = '1'))
  else                 '0';
  cpu_cache_l0_sel  <= '1' when (cache_l0_valid = '1') and (cache_l0_addr = i_cpu_addr)                                                                 -- Flag CPU read Data from Cache L0
  else                 '0';
  cpu_otp_rd_sel    <= '1' when (otp_addr_latch = i_cpu_addr)                                                                                           -- Flag CPU read Data from currently Read Address
  else                 '0';
  cpu_array_sel     <= '1' when (flag_cpu_rd = '1') and (cpu_cache_l0_sel = '0') and (cpu_otp_rd_sel = '0')                                             -- Flag CPU read completely new Address
  else                 '0';
  flag_fsm_idle     <= '1' when (NEXT_STATE = ST1_IDLE)
  else                 '0';
  flag_fsm_read     <= '1' when (SYS_STATE = ST2_CPU_CK1) or (SYS_STATE = ST17_CPU_CK0)
  else                 '0';
  flag_fsm_pgm      <= '1' when (SYS_STATE = ST3_VPP_ON) or (SYS_STATE = ST4_WRITE_VRR) or (SYS_STATE = ST5_WRITE_SEL_WE)
  else                 '1' when (SYS_STATE = ST6_WRITE_AD1) or (SYS_STATE = ST7_WRITE_AD2) or (SYS_STATE = ST8_WRITE_CK1) or (SYS_STATE = ST9_WRITE_CK0)
  else                 '1' when (SYS_STATE = ST10_READ_VRR) or (SYS_STATE = ST11_READ_A) or (SYS_STATE = ST12_READ_CK1) or (SYS_STATE = ST13_READ_CK0)
  else                 '1' when (SYS_STATE = ST14_READ_EVAL) or (SYS_STATE = ST15_FINISH) or (SYS_STATE = ST16_VPP_OFF)
  else                 '0';
  
  reread_mux_l0     <= '1' when (cpu_cache_l0_sel = '1') and (flag_cpu_rd = '1')
  else                 '0';
  
  otp_cache_ctrl : process (flag_cpu_rd, cpu_cache_l0_sel, cache_l0_valid) is -- flag_fsm_idle flag_fsm_read flag_fsm_pgm
  begin
    if    (flag_cpu_rd = '0') and (cache_l0_valid = '0') then      -- Wait First CPU Read
      start_otp_read  <= '0';
    elsif (flag_cpu_rd = '1') and (cache_l0_valid = '0') then      -- Initial Read
      start_otp_read  <= '1';
    elsif (flag_cpu_rd = '1') and (cpu_cache_l0_sel = '1') then    -- CPU read data from Cache L0, Update L0, L1 Latch old L0
      start_otp_read  <= '1';
    elsif (flag_cpu_rd = '1') and (cpu_cache_l0_sel = '0') then    -- CPU read data not in Cache
      start_otp_read  <= '1';
    else
      start_otp_read  <= '0';
    end if;
    
    if    (flag_cpu_rd = '0') then                                -- No CPU Read
      en_cache_l0_read  <= '0';
    elsif (flag_cpu_rd = '1') and (cpu_cache_l0_sel = '1') then   -- Data from Cache L0
      en_cache_l0_read  <= '1';
    else--(flag_cpu_rd = '1') and (cpu_cache_l0_sel = '0')
      en_cache_l0_read  <= '0';
    end if;
  end process;
  
  -------------------------------------------------------------------------------
  -- OTP : BIST Control Register JTAG_IR=0x6E
  -------------------------------------------------------------------------------
  otp_ctrl_reg : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_pgm   <= '0';
      otp_read  <= '1';
      en_soak   <= '0';
      stress    <= '0';
      sel_trp   <= '0';
      sel_rd    <= '0';
      sel_mpp   <= '0';
      sel_mrr   <= '0';
      sel_mr    <= '0';
      max_soak  <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if (i_update_dr_pulse = '1') and (ir_otpbist_ctrl_clk = '1') then         -- JTAG access
        otp_pgm   <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_OTP_PGM);
        otp_read  <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_OTP_READ);
        en_soak   <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_EN_SOAK);
        stress    <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_STRESS);
        sel_trp   <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_SEL_TRP);
        sel_rd    <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_SEL_RD);
        sel_mpp   <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_SEL_MPP);
        sel_mrr   <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_SEL_MRR);
        sel_mr    <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_SEL_MR);
        max_soak  <= i_jtag_dsr((c_dsr_width-BL_OTPBISTCTRL+BIT_MAX_SOAK_MSB) downto (c_dsr_width-BL_OTPBISTCTRL+BIT_MAX_SOAK_LSB));
      end if;
    end if;
  end process otp_ctrl_reg;
  bist_ctrl(BIT_BIST_CTRL3)   <= '0'; -- reserved
  bist_ctrl(BIT_BIST_CTRL11)  <= '0'; -- reserved
  bist_ctrl(BIT_BIST_CTRL15)  <= '0'; -- reserved
  
  max_soak_val  <= MAX_NO_SOAK_PULSES - unsigned('0' & max_soak);  -- 10 - (7..0) = 3..10
  
  stress_stat  <= stress;
  
  otp_ctrl_soak_bit : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      soak  <= '0';
    elsif rising_edge(i_clk_sys) then
      if (i_update_dr_pulse = '1') and (ir_otpbist_ctrl_clk = '1') then         -- JTAG access
        soak  <= i_jtag_dsr(c_dsr_width-BL_OTPBISTCTRL+BIT_SOAK);
      elsif (cpu_bistctrl_sel_lsb = '1') and (i_cpu_rw = '0') then              -- CPU access
        soak  <= i_cpu_dout(BIT_SOAK);
      elsif (set_soak = '1') then                                               -- BIST FSM
        soak  <= '1';
      elsif (clr_soak = '1') then                                               -- BIST FSM
        soak  <= '0';
      end if;
    end if;
  end process otp_ctrl_soak_bit;
  
  -------------------------------------------------------------------------------
  -- OTP : BIST/TEST Config Register JTAG_IR=0x6F
  -------------------------------------------------------------------------------
  otp_conf_reg : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      trp      <= (others => '0');
      rd_mode  <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if (i_update_dr_pulse = '1') and (ir_otpbist_conf_clk = '1') then         -- JTAG access
        trp      <= i_jtag_dsr((c_dsr_width-BL_OTPBISTCONF+BIT_TRP_MSB) downto (c_dsr_width-BL_OTPBISTCONF+BIT_TRP_LSB));
        rd_mode  <= i_jtag_dsr((c_dsr_width-BL_OTPBISTCONF+BIT_RD_MODE_MSB) downto (c_dsr_width-BL_OTPBISTCONF+BIT_RD_MODE_LSB));
      elsif (cpu_bistconf_sel_lsb = '1') and (i_cpu_rw = '0') then                 -- CPU access
        trp      <= i_cpu_dout(BIT_TRP_MSB downto BIT_TRP_LSB);
      elsif (cpu_bistconf_sel_msb = '1') and (i_cpu_rw = '0') then                 -- CPU access
        rd_mode  <= i_cpu_dout(BIT_RD_MODE_MSB downto BIT_RD_MODE_LSB);
      end if;
    end if;
  end process otp_conf_reg;
  eccerr_l  <= i_eccerr_l;
  eccerr_h  <= i_eccerr_h;
  bist_conf(BIT_BIST_CONF7)   <= '0'; -- reserved
  bist_conf(BIT_BIST_CONF10)  <= '0'; -- reserved
  bist_conf(BIT_BIST_CONF11)  <= '0'; -- reserved
  
  mux_trp  <= VAL_READ_CK1                  when (stress = '0') and (sel_trp = '0')
  else        VAL_ZERO                      when (trp(BL_TRP-1 downto 1) = TRP_SMALL)
  else        ZEROFILL_TRP & (unsigned(trp) - to_unsigned(1, BL_TRP));
  
  -------------------------------------------------------------------------------
  -- OTP : BIST Status Register JTAG_IR=0x70
  -------------------------------------------------------------------------------
  prog_bit    <= std_logic_vector(bit_cnt);
  bist_stat(BIT_BIST_STAT6)   <= '0'; -- reserved
  done        <= done_last_bit;
  soak_pulse  <= std_logic_vector(soak_cnt);
  soak_stat   <= soak;
  
  busy_ctrl : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      busy    <= '0';
      en_vrr  <= '0';
    elsif rising_edge(i_clk_sys) then
      if (clr_busy = '1') then
        busy  <= '0';
      elsif (clr_stat = '1') then
        busy  <= '1';
      end if;
      if    (set_vrr_en = '1') then
        en_vrr <= '1';
      elsif (clr_vrr_en = '1') then
        en_vrr <= '0';
      end if;
    end if;
  end process busy_ctrl;
  
  fail_ctrl : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      fail0  <= '0';
      fail1  <= '0';
    elsif rising_edge(i_clk_sys) then
      if (clr_stat = '1') then
        fail0  <= '0';
      elsif (set_fail0 = '1') then
        fail0  <= '1';
      end if;
      if (clr_stat = '1') then
        fail1  <= '0';
      elsif (set_fail1 = '1') then
        fail1  <= '1';
      end if;
    end if;
  end process fail_ctrl;
  
  -------------------------------------------------------------------------------
  -- OTP : BIST MRR Register 
  -------------------------------------------------------------------------------
  cpu_mrr(3 downto 0)               <= c_otp_vrr_dat;
  cpu_mrr(c_otp_wl_mrr-1 downto 4)  <= (others => '0');
  
  -------------------------------------------------------------------------------
  -- OTP : BIST MPP Register
  -------------------------------------------------------------------------------
  cpu_otp_mpp_reg : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      cpu_mpp(3 downto 0)  <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if (cpu_otpmpp_sel = '1') and (i_cpu_rw = '0') then                 -- CPU access
        cpu_mpp(3 downto 0)  <= i_cpu_dout(3 downto 0);
      end if;
    end if;
  end process cpu_otp_mpp_reg;
  cpu_mpp(c_otp_wl_mpp-1 downto 4)  <= (others => '0');
  
  -- OTP : Input
  -------------------------------------------------------------------------------
  otp_input_sel_pgm : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_sel_pgm  <= '0';
    elsif rising_edge(i_clk_sys) then
      if    (set_otp_sel = '1') then
        otp_sel_pgm  <= '1';
      elsif (clr_otp_sel = '1') then
        otp_sel_pgm  <= '0';
      end if;
    end if;
  end process otp_input_sel_pgm;
  otp_sel  <= otp_sel_pgm or otp_sel_rd;
  
  otp_input_sel_rd : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_sel_rd  <= '0';
    elsif rising_edge(i_clk_sys) then
      if    (set_otp_sel_rd = '1') then
        otp_sel_rd  <= '1';
      elsif (clr_otp_sel_rd = '1') then
        otp_sel_rd  <= '0';
      end if;
    end if;
  end process otp_input_sel_rd;
  
  otp_input_oe : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_oe  <= '0';
    elsif rising_edge(i_clk_sys) then
      if    (set_otp_oe = '1') or (i_otp_tst = '1') then
        otp_oe  <= '1';
      elsif (clr_otp_oe = '1') then
        otp_oe  <= '0';
      end if;
    end if;
  end process otp_input_oe;
  
  otp_input_we : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_we   <= '0';
    elsif rising_edge(i_clk_sys) then
      if    (set_otp_we = '1') then
        otp_we  <= '1';
      elsif (clr_otp_we = '1') then
        otp_we  <= '0';
      end if;
    end if;
  end process otp_input_we;
  
  otp_input_ck : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_ck      <= '0';
    elsif rising_edge(i_clk_sys) then
      if    ((set_otp_ck = '1') and (stress = '1')) then                -- Both 32bit and 12bit active
        otp_ck     <= '1';
      elsif ((set_otp_ck = '1') and (NEXT_STATE = ST2_CPU_CK1)) then    -- Read 32bit + 12bit / CPU Application
        otp_ck     <= '1';
      elsif ((set_otp_ck = '1') and (NEXT_STATE = ST12_READ_CK1)) then  -- Read 32bit + 12bit / BIST Check
        otp_ck     <= '1';
      elsif ((set_otp_ck = '1') and (bit_cnt < THR_BIT)) then           -- Selected Data for programming
        otp_ck     <= '1';
      elsif (clr_otp_ck = '1') then
        otp_ck     <= '0';
      end if;
    end if;
  end process otp_input_ck;
  
  otp_input_envpp : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      en_vpp   <= '0';
    elsif rising_edge(i_clk_sys) then
      if    (set_otp_vpp = '1') then
        en_vpp  <= '1';
      elsif (clr_otp_vpp = '1') then
        en_vpp  <= '0';
      end if;
    end if;
  end process otp_input_envpp;
  
  otp_din  <= (std_logic_vector(unsigned(OTP_DATA_ONE) sll to_integer(bit_cnt))) when (stress_stat = '0') -- 26.09.2016 DPOL Stress Data Corrected
  else        (others => '0') ;
  
  mux_otp_addr  <= i_jtag_addr    when (i_otp_tst = '1')
  else             otp_addr_latch when (busy = '0')
  else             cache_l0_addr;  -- (busy = '1')
  
  otp_read_addr_latch : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_addr_latch   <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if (en_reload_addr = '1') then                                           -- Fix New Address for future read
        otp_addr_latch  <= i_cpu_addr;
      elsif (start_otp_read = '1') and (flag_fsm_idle = '1') then
        if (rst_cache_l0 = '1') then                                           -- Reread : Address From CPU (from SLEEP/PGM)
          otp_addr_latch  <= i_cpu_addr;
        elsif (cpu_cache_l0_sel = '1') then                                    -- CPU Read L0 : 
          otp_addr_latch  <= std_logic_vector(unsigned(cache_l0_addr) + 1);
        else                                                                   -- Initial Read : Address From CPU / 
          otp_addr_latch  <= i_cpu_addr;
        end if;
      end if;
    end if;
  end process otp_read_addr_latch;
  
  ok_addr_latch  <= '1' when (otp_addr_latch = std_logic_vector(unsigned(cache_l0_addr) + 1)) and (cpu_cache_l0_sel = '1')
  else              '1' when (otp_addr_latch = i_cpu_addr) and (cpu_array_sel = '1')
  else              '0';
  
  otp_input_vrr : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_vrr_mode   <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if (en_sel_otp_vrr = '1') then
        case sel_otp_vrr is
          when "00"   =>
            otp_vrr_mode  <= "00";
          when "01"   =>
            otp_vrr_mode  <= "01";
          when others => -- "10" & "11"
            otp_vrr_mode  <= "10";
        end case;
      end if;
    end if;
  end process otp_input_vrr;
  
  otp_vrr  <= VAL_VRR0 when (otp_vrr_mode = "00")
  else        VAL_VRR1 when (otp_vrr_mode = "01")  -- ime, changed "10" to "01"
  else        VAL_VRR2;
  
  otp_mrr  <= i_otp_mrr        when (sel_mrr = '1')
  else        x"000" & cpu_mrr(3 downto 0) when (busy = '1') and (SYS_STATE = ST16_VPP_OFF)
  else        x"000" & otp_vrr             when (busy = '1')
  else        cpu_mrr;
  
  otp_mr   <= i_otp_mr when (sel_mr = '1')
  else        x"00"    when (busy = '1')
  else        i_cpu_otp_mr;
  
  otp_mpp  <= i_otp_mpp when (sel_mpp = '1')
  else        cpu_mpp   when (busy = '1')      -- Auto-Programming Mode: configure Trim Bits
  else        x"00";
  
  -------------------------------------------------------------------------------
  -- OTP : Output
  -------------------------------------------------------------------------------
  otp_output_data : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      w_q_diff  <= (others => '0');
      
      flag_err_unprog  <= '0';
    elsif rising_edge(i_clk_sys) then
      if    (en_latch_dr = '1') then
        w_q_diff  <= otp_dr xor i_latch_otp_dw;          -- compare : read value and write value
      end if;
      
      if    (en_latch_dr = '1') and (((otp_dr xor i_latch_otp_dw) and otp_dr)  = OTP_DATA_ZERO) then
        flag_err_unprog  <= '0';
      elsif (en_latch_dr = '1') and (((otp_dr xor i_latch_otp_dw) and otp_dr) /= OTP_DATA_ZERO) then
        flag_err_unprog  <= '1';
      end if;
    end if;
  end process otp_output_data;
  
  flag_equal       <= '1' when (w_q_diff = OTP_DATA_ZERO)
  else                '0';
  
  -------------------------------------------------------------------------------
  -- OTP : Programming BIT Counter
  -------------------------------------------------------------------------------
  otp_prog_bit_counter : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      bit_cnt        <= (others => '0');
      done_last_bit  <= '0';
    elsif rising_edge(i_clk_sys) then
      if    (start_bit_cnt = '1') then
        bit_cnt        <= (others => '0');
        done_last_bit  <= '0';
      elsif (incr_bit_cnt = '1') and (bit_cnt < MAX_BIT) then
        bit_cnt  <= bit_cnt + 1;
      elsif (incr_bit_cnt = '1') and (bit_cnt = MAX_BIT) then       -- Normal/Soak PGM
        done_last_bit  <= '1';
      elsif (done_bit_cnt = '1') then                               -- Stress once PGM with Data=0
        bit_cnt  <= (others => '0');
        done_last_bit  <= '1';
      end if;
    end if;
  end process otp_prog_bit_counter;
  
  -------------------------------------------------------------------------------
  -- OTP : SOAK Counter and Read2
  -------------------------------------------------------------------------------
  soak_ctrl : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      sel_read2   <= '0';
      soak_cnt  <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if    (set_read2 = '1') then
        sel_read2  <= '1';
      elsif (clr_read2 = '1') then
        sel_read2  <= '0';
      end if;
      if (clr_stat = '1') then
        soak_cnt  <= (others => '0');
      elsif (incr_soak_cnt = '1') then
        soak_cnt  <= soak_cnt + 1;
      end if;
    end if;
  end process soak_ctrl;
  
  -------------------------------------------------------------------------------
  -- FSM: OTP Control
  -------------------------------------------------------------------------------
  -- state register
  -------------------------------------------------------------------------------
  state_process : process (i_nrst, i_clk_sys) is begin
    if (i_nrst = '0') then
      SYS_STATE <= ST0_SLEEP;
    elsif rising_edge(i_clk_sys) then
      SYS_STATE <= NEXT_STATE;
    end if;
  end process;
  
  flag_bitprog_1  <= '1' when (soak = '0') and (i_latch_otp_dw(to_integer(bit_cnt)) = '1')
  else               '1' when (soak = '1') and (w_q_diff(to_integer(bit_cnt)) = '1') 
  else               '0';
  
  flag_jtag_rd     <= '1' when ((i_otp_tst = '1') and (i_start_otp_read = '1'))
  else                '0';
  
  fsm_process : process (SYS_STATE, i_sleep_mode, i_start_otp_pgm, stress_stat, cpu_cache_sel, flag_cnt_zero, flag_cnt_of, en_soak, flag_cpu_rd,
                         flag_jtag_rd, mux_trp, soak_cnt, sel_read2, flag_equal, flag_err_unprog, soak_stat, done_last_bit, flag_bitprog_1, flag_zero_trp, VAL_WRITE_CK1, VAL_SOAK_CK1, max_soak_val) is
  begin
    ------------------------------------ 
    en_cnt           <= '0';
    en_load_cnt      <= '0';
    cnt_val          <= (others => '1');
    clr_hold         <= '0';
    
    rst_cache_l0     <= '0';
    en_latch_cl0     <= '0';
    en_reload_addr   <= '0';
    
    start_bit_cnt    <= '0';
    incr_bit_cnt     <= '0';
    done_bit_cnt     <= '0';
    en_shft_data     <= '0';
    latch_cpu_data   <= '0';
    latch_diff_data  <= '0';
    en_clr_data      <= '0';
    set_read2        <= '0';
    clr_read2        <= '0';
    incr_soak_cnt    <= '0';
    en_sel_otp_vrr   <= '0';
    sel_otp_vrr      <= "00";
    
    set_vrr_en       <= '0';
    clr_vrr_en       <= '0';
    set_otp_vpp      <= '0';
    set_otp_sel      <= '0';
    set_otp_sel_rd   <= '0';
    set_otp_we       <= '0';
    set_otp_ck       <= '0';
    set_otp_oe       <= '0';
    clr_otp_vpp      <= '0';
    clr_otp_sel      <= '0';
    clr_otp_sel_rd   <= '0';
    clr_otp_we       <= '0';
    clr_otp_ck       <= '0';
    clr_otp_oe       <= '1';
    clr_stat         <= '0';
    en_latch_dr      <= '0';
    clr_busy         <= '0';
    
    set_fail1        <= '0';
    set_fail0        <= '0';
    set_soak         <= '0';
    clr_soak         <= '0';
    ------------------------------------ 
    case (SYS_STATE) is
      when ST1_IDLE =>
        if    (i_sleep_mode = '1') then
          clr_vrr_en          <= '1';
          rst_cache_l0        <= '1';
          next_state          <= ST0_SLEEP;
        elsif (flag_cpu_rd = '1') and (cpu_cache_sel = '1') and (stress_stat = '0') then     --                        - CPU Read from OTP cache
          clr_hold            <= '1';
          set_otp_oe          <= '1';
          clr_otp_oe          <= '0';
          next_state          <= ST1_IDLE;
        elsif (flag_cpu_rd = '1') and (flag_zero_trp = '1') then -- (cpu_cache_sel = '0') or (stress_stat = '1')       - CPU Read from OTP TRP=0
          set_otp_oe          <= '1';
          clr_otp_oe          <= '0';
          set_otp_sel_rd      <= '1';
          clr_otp_we          <= '1';
          en_reload_addr      <= '1';
          next_state          <= ST20_SEL_READ;
        elsif (flag_cpu_rd = '1') then -- (flag_zero_trp = '0') and (cpu_cache_sel = '0') or (stress_stat = '1')       - CPU Read from OTP / TRP>0
          set_otp_sel_rd      <= '1';
          clr_otp_we          <= '1';
          en_reload_addr      <= '1';
          next_state          <= ST20_SEL_READ;
        elsif (flag_jtag_rd = '1') and (flag_zero_trp = '1') then
          set_otp_oe          <= '1';
          clr_otp_oe          <= '0';
          set_otp_sel_rd      <= '1';
          next_state          <= ST20_SEL_READ;
        elsif (flag_jtag_rd = '1') then -- flag_zero_trp = '0'
          set_otp_sel_rd      <= '1';
          next_state          <= ST20_SEL_READ;
        elsif (i_start_otp_pgm = '1') and (stress_stat = '0') then
          set_otp_vpp         <= '1';
          en_load_cnt         <= '1';
          latch_cpu_data      <= '1';
          clr_stat            <= '1';
          cnt_val             <= VAL_VPP_ON;
          next_state          <= ST3_VPP_ON;
        elsif (i_start_otp_pgm = '1') then -- (stress_stat = '1')
          set_otp_vpp         <= '1';
          en_load_cnt         <= '1';
          clr_stat            <= '1';
          cnt_val             <= VAL_VPP_ON; -- can be zero time
          next_state          <= ST3_VPP_ON;
        else
          clr_hold            <= '1';
          next_state          <= ST1_IDLE;
        end if; 
      when ST20_SEL_READ =>
        set_otp_ck          <= '1';
        en_load_cnt         <= '1';
        cnt_val             <= mux_trp;
        next_state          <= ST2_CPU_CK1;
      when ST2_CPU_CK1 =>
        if (flag_zero_trp = '1') then           -- 20.09.2016 updated
          clr_otp_ck          <= '1';
          clr_otp_sel_rd      <= '1';
          set_otp_oe          <= '1';
          clr_otp_oe          <= '0';
          next_state          <= ST17_CPU_CK0;
        elsif (flag_cnt_zero = '1') then
          clr_otp_ck          <= '1';
          clr_otp_sel_rd      <= '1';
          set_otp_oe          <= '1';
          clr_otp_oe          <= '0';
          next_state          <= ST17_CPU_CK0;  -- 12.09.2016 new Mode added DPOL
        else
          set_otp_oe          <= '1';
          clr_otp_oe          <= '0';
          en_cnt              <= '1';
          next_state          <= ST2_CPU_CK1;
        end if;
      when ST17_CPU_CK0 =>
        if (flag_zero_trp = '1') then           -- 20.09.2016 updated
          clr_hold            <= '1';
          en_latch_cl0        <= '1';
          next_state          <= ST1_IDLE;
        else
          clr_hold            <= '1';
          en_latch_cl0        <= '1';
          next_state          <= ST1_IDLE;
        end if;
      when ST3_VPP_ON =>
        if (flag_cnt_zero = '1') then
          en_load_cnt         <= '1';
          cnt_val             <= VAL_VRR_SETUP;
          next_state          <= ST4_WRITE_VRR;
        else
          en_cnt              <= '1';
          next_state          <= ST3_VPP_ON;
        end if;
       when ST4_WRITE_VRR =>
        if (flag_cnt_zero = '1') then
          set_otp_sel         <= '1';
          set_otp_we          <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= VAL_SEL_WE;
          next_state          <= ST5_WRITE_SEL_WE;
        else
          en_cnt              <= '1';
          next_state          <= ST4_WRITE_VRR;
        end if;
       when ST5_WRITE_SEL_WE =>
        if (flag_cnt_zero = '1') then
          start_bit_cnt       <= '1';
          next_state          <= ST6_WRITE_AD1;
        else
          en_cnt              <= '1';
          next_state          <= ST5_WRITE_SEL_WE;
        end if;
       when ST6_WRITE_AD1 =>
        if    (done_last_bit = '0') and (stress_stat = '0') and (flag_bitprog_1 = '1') then  --              - PGM normal BIT1
          en_shft_data        <= '1';
          next_state          <= ST7_WRITE_AD2;
        elsif (done_last_bit = '0') and (stress_stat = '0') then --(flag_bitprog_1 = '0')                    - PGM skip BIT0 (increment bit_cnt)
          incr_bit_cnt        <= '1';
          next_state          <= ST6_WRITE_AD1;
        elsif (done_last_bit = '0') then -- (stress_stat = '1')                                              - Stress PGM once
          en_clr_data         <= '1';
          done_bit_cnt        <= '1';
          next_state          <= ST7_WRITE_AD2;
        elsif (stress_stat = '1') then -- (done_last_bit = '1')                                              - Done + Stress -> finish
          clr_otp_we          <= '1';
          next_state          <= ST15_FINISH;
        elsif (soak_stat = '0') then   -- (done_last_bit = '1') and (stress_stat = '0')                      - Done + SOAK=0 -> check programmed data
          clr_read2           <= '1';
          clr_otp_we          <= '1';
          en_sel_otp_vrr      <= '1';
          sel_otp_vrr         <= "01";                -- VRR1 for initial read check / PROG
          en_load_cnt         <= '1';
          cnt_val             <= VAL_VRR_SETUP;
          next_state          <= ST10_READ_VRR;
        else -- (done_last_bit = '1') and (soak_stat = '1')                                                  - Done + SOAK=1 -> check soaked data
          incr_soak_cnt       <= '1';
          set_read2           <= '1';
          clr_otp_we          <= '1';
          en_sel_otp_vrr      <= '1';
          sel_otp_vrr         <= "10";                -- VRR2 for initial read check / SOAK
          en_load_cnt         <= '1';
          cnt_val             <= VAL_VRR_SETUP;
          next_state          <= ST10_READ_VRR;
        end if;
      when ST7_WRITE_AD2 =>
        if (soak_stat = '0') then
          set_otp_ck          <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= unsigned(   VAL_WRITE_CK1);
          next_state          <= ST8_WRITE_CK1;
        else
          set_otp_ck          <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= unsigned(   VAL_SOAK_CK1);
          next_state          <= ST8_WRITE_CK1;
        end if;
      when ST8_WRITE_CK1 =>
        if (flag_cnt_zero = '1') then
          clr_otp_ck          <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= VAL_WRITE_CK0;
          next_state          <= ST9_WRITE_CK0;
        else
          en_cnt              <= '1';
          next_state          <= ST8_WRITE_CK1;
        end if;
      when ST9_WRITE_CK0 =>
        if (flag_cnt_zero = '1') then
          incr_bit_cnt        <= '1';
          next_state          <= ST6_WRITE_AD1;
        else
          en_cnt              <= '1';
          next_state          <= ST9_WRITE_CK0;
        end if;
      when ST10_READ_VRR =>
        if (flag_cnt_zero = '1') then
          next_state          <= ST11_READ_A;
        else
          en_cnt              <= '1';
          next_state          <= ST10_READ_VRR;
        end if;
      when ST11_READ_A =>
        set_otp_ck          <= '1';
        en_load_cnt         <= '1';
        cnt_val             <= mux_trp;
        next_state          <= ST12_READ_CK1;
      when ST12_READ_CK1 =>
        if (flag_cnt_zero = '1') then
          clr_otp_ck          <= '1';
          set_otp_oe          <= '1';
          clr_otp_oe          <= '0';
          en_load_cnt         <= '1';
          cnt_val             <= VAL_READ_CK0;
          next_state          <= ST13_READ_CK0;
        else
          en_cnt              <= '1';
          next_state          <= ST12_READ_CK1;
        end if;
      when ST13_READ_CK0 =>
        if (flag_cnt_zero = '1') then
          en_latch_dr         <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= VAL_READ_CK0;
          next_state          <= ST14_READ_EVAL;
        else
          clr_otp_oe          <= '0';
          en_cnt              <= '1';
          next_state          <= ST13_READ_CK0;
        end if;
      when ST14_READ_EVAL =>
        if    (flag_equal = '1') then
          next_state          <= ST15_FINISH;
        elsif (flag_err_unprog = '1') then                 -- (flag_equal = '0')
          set_fail0           <= '1';
          set_fail1           <= '0';                                                 -- 27.09.2016 DPOL FAIL1 - not flag for '1' keep '0' value
          next_state          <= ST15_FINISH;
        elsif (sel_read2 = '0') and (en_soak = '0') then   -- (flag_equal = '0') and (flag_err_unprog = '0')
          set_fail1           <= '1';
          next_state          <= ST15_FINISH;
        elsif (sel_read2 = '0') then                       -- (flag_equal = '0') and (flag_err_unprog = '0') and (en_soak = '1')
          latch_diff_data     <= '1';
          en_sel_otp_vrr      <= '1';
          sel_otp_vrr         <= "00";                     -- VRR0 for soak programming
          set_soak            <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= VAL_VRR_SETUP;
          next_state          <= ST4_WRITE_VRR;
        elsif (soak_cnt >= max_soak_val) then                  -- (sel_read2 = '1') ...
          set_fail1           <= '1';
          next_state          <= ST15_FINISH;
        else                                               -- (flag_equal = '0') so recheck by READ1
          en_sel_otp_vrr      <= '1';
          sel_otp_vrr         <= "01";                     -- VRR1 for recheck
          clr_read2           <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= VAL_VRR_SETUP;
          next_state          <= ST10_READ_VRR;
        end if;
      when ST15_FINISH =>
        clr_otp_sel         <= '1';
        clr_otp_vpp         <= '1';
        en_sel_otp_vrr      <= '1';
        sel_otp_vrr         <= "00";                       -- VRR0 for cpu read
        clr_soak            <= '1';
        clr_read2           <= '1';
        en_load_cnt         <= '1';
        cnt_val             <= VAL_VRR_SETUP;
        next_state          <= ST16_VPP_OFF;
      when ST16_VPP_OFF =>
        if (flag_cnt_zero = '1') then
          rst_cache_l0        <= '1';
          clr_busy            <= '1';
          next_state          <= ST1_IDLE;
        else
          en_cnt              <= '1';
          next_state          <= ST16_VPP_OFF;
        end if;
      when others  =>  -- ST0_SLEEP
        if    (i_sleep_mode = '0') and (flag_cnt_zero = '1') then
          rst_cache_l0        <= '1';
          next_state          <= ST1_IDLE;
        elsif (i_sleep_mode = '0') and (flag_cnt_of = '1') then
          set_vrr_en          <= '1';
          en_load_cnt         <= '1';
          cnt_val             <= VAL_VPP_ON;
          next_state          <= ST0_SLEEP;
        elsif (i_sleep_mode = '0') then
          set_vrr_en          <= '1';
          en_cnt              <= '1';
          next_state          <= ST0_SLEEP;
        else
          en_load_cnt         <= '1';
          cnt_val             <= VAL_VPP_ON;
          next_state          <= ST0_SLEEP;
        end if;
    end case;
  end process fsm_process;
  
  flag_cnt_zero  <= '1' when (wait_cnt = VAL_ZERO)
  else              '0';
  flag_cnt_of    <= '1' when (wait_cnt = VAL_OF)
  else              '0';
  flag_zero_trp  <= '1' when (mux_trp = VAL_ZERO)  -- Flag for Null Read Time  // or (mux_trp = VAL_ONE)
  else              '0';
  
  cnt_process : process (i_nrst, i_clk_sys) is begin
    if (i_nrst = '0') then
      wait_cnt  <= (others => '1');
    elsif rising_edge(i_clk_sys) then
      if    (en_load_cnt = '1') then
        wait_cnt  <= cnt_val;
      elsif (en_cnt = '0') then
        if (wait_cnt /= VAL_OF) then
          wait_cnt  <= (others => '1');
        end if;
      elsif (wait_cnt > 0) then
        wait_cnt  <= wait_cnt - 1;
      end if;
    end if;
  end process cnt_process;
  
end RTL;
