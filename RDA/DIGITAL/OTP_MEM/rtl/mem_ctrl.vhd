-------------------------------------------------------------------------------
-- Title       : MEM_CTRL
-- Project     : E13707 Airbag
-------------------------------------------------------------------------------
-- Description :
-------------------------------------------------------------------------------
-- Subblocks   : 
-------------------------------------------------------------------------------
-- File        : mem_ctrl.vhd
-- Author      : Denis Poliakov (DPOL) ELSPB
-- Company     : ELMOS Semiconductor AG
-- Created     : 17.04.2017
-- Last update : 14.06.2017
-------------------------------------------------------------------------------
-- Copyright (c) 2017 ELMOS Semiconductor AG
-------------------------------------------------------------------------------
-- Revisions   :
-- Date        Version  Author  Description
-- 05.06.2017   1.0     dpol    initial release
-- 13.06.2017   1.1     dpol    synthesis error corrected
-- 14.06.2017   1.2     dpol    pointer processing corrected
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

library OTP_MEM;
use OTP_MEM.mem_pkg.all;

library JTAG;
use JTAG.jtag_tap_pkg.t_jtag_bus;

library digital;
use digital.digital_pkg.target_technology_TSMC;
use digital.digital_pkg.target_technology_FPGA;

entity mem_ctrl is
  port (
    -- system
    i_rst_n          : in  std_logic;  -- low-active reset
    i_sys_clk        : in  std_logic;  -- system clock 1
    i_atpg_mode      : in  std_logic;  -- ATPG : SCAN or IDDQ mode
    
    -- System Control
    i_off_mem        : in  std_logic;  -- Switch off memory
    i_update_mem     : in  std_logic;  -- update memory / from FSM
    i_sys_state      : in  std_logic_vector(5 downto 0);  -- c_sys_power_off = 000001; c_sys_wake_up = 000010:  c_sys_initial = 000100
    o_rdy_mem        : out std_logic;  -- memory ready
    o_ecc_err        : out std_logic;  -- Status of ECC error: '0' - data ok, '1' - single error
    o_ecc_fail       : out std_logic;  -- Status of ECC error: '0' - data ok, '1' - double error
    o_nvm_err        : out std_logic;  -- Status of NVM: '1' - 3 times read fail
    o_data           : out std_logic_vector(179 downto 0);
    
    -- OTP control
    o_sleep_mode     : out std_logic;  -- 
    
    -- ip bus interface
    i_ip_bus         : in  t_ip_bus;
    o_ip_bus         : out t_ip_bus;
    
    -- test/JTAG interface
    i_jtag_bus       : in  t_jtag_bus;
    o_jtag_bus       : out t_jtag_bus
  );
end mem_ctrl;

architecture MEM_CTRL_RTL of mem_ctrl is
  -------------------------------------------------------------------------------
  -- subblocks
  -------------------------------------------------------------------------------
  component DW_ecc 
  generic(
    width    : integer;
    chkbits  : integer;
    synd_sel : integer
  );
  port(
    correct_n  : in  std_logic;
    gen        : in  std_logic;
    datain     : in  std_logic_vector(179 downto 0);
    chkin      : in  std_logic_vector(11 downto 0);
    dataout    : out std_logic_vector(179 downto 0);
    chkout     : out std_logic_vector(11 downto 0);
    err_detect : out std_logic;
    err_multpl : out std_logic
  );
  end component;
  -------------------------------------------------------------------------------
  
  -------------------------------------------------------------------------------
  -- signals
  -------------------------------------------------------------------------------
  signal otp_slp     : std_logic;
  signal otp_hold    : std_logic;
  signal wait_latch  : std_logic;
  signal active_read : std_logic;
  
  -- OTP Array : Pointer Control
  constant BL_PTR_CNT   : integer := 2;
  signal   ptr_cnt      : unsigned((BL_PTR_CNT-1) downto 0); -- Counter for Pointer Words
  constant VAL_PTR_MAX  : unsigned((BL_PTR_CNT-1) downto 0) := "11"; -- 
  
  constant BL_PTR_BIT   : integer := 4;
  signal   blk_cnt      : unsigned((BL_PTR_BIT-1) downto 0); -- Counter for Pointer Bits
  constant VAL_BLK_ZERO : unsigned((BL_PTR_BIT-1) downto 0) := "0000"; -- 
  constant VAL_BLK_MAX  : unsigned((BL_PTR_BIT-1) downto 0) := "1011"; -- d11
  
  signal valid_ptr_bit  : std_logic;
  signal err_ptr_bit    : std_logic;
  signal err_ptr_empty  : std_logic;
  signal flag_blk_empty : std_logic;
  signal flag_blk_full  : std_logic;
  signal flag_ptr_err0  : std_logic;
  signal flag_ptr_err1  : std_logic;
  
  constant BL_BLK_WORD   : integer := 4;
  signal   blk_word      : unsigned((BL_BLK_WORD-1) downto 0); -- Counter for Word in Block
  constant VAL_WORD_MAX  : unsigned((BL_BLK_WORD-1) downto 0) := "1110"; -- d14
  signal flag_last_word  : std_logic;
  signal flag_rdy_words  : std_logic;
  signal flag_rdy_ecc    : std_logic;
  constant ADDR_ECC      : std_logic_vector((BL_BLK_WORD-1) downto 0) := "1111";
  
  -- OTP Array : Data Read Control
  constant BL_OTP_ADDR    : integer := 12;
  constant BL_OTP_DATA    : integer := 12;
  signal   otp_addr       : std_logic_vector((BL_OTP_ADDR-1) downto 0); -- 
  signal   otp_dr         : std_logic_vector((BL_OTP_DATA-1) downto 0); -- 
  signal   otp_ptr0       : std_logic_vector((BL_OTP_DATA-1) downto 0); -- 
  signal   otp_ptr1       : std_logic_vector((BL_OTP_DATA-1) downto 0); -- 
  signal   otp_ptr2       : std_logic_vector((BL_OTP_DATA-1) downto 0); -- 
  signal   valid_ptr      : std_logic_vector(2 downto 0); -- 
  
  constant fill_addr_ptr  : std_logic_vector((BL_OTP_ADDR-BL_PTR_CNT-1) downto 0) := (others => '0');
  constant fill_addr_blk  : std_logic_vector((BL_OTP_ADDR-BL_PTR_BIT-BL_BLK_WORD-1) downto 0) := (others => '0');
  
  -- OTP Array : Data + Ecc
  constant BL_MEM_DAT    : integer := 180;
  constant BL_MEM_ECC    : integer :=  12;
  signal   mem_dat       : std_logic_vector((BL_MEM_DAT-1) downto 0); -- 
  signal   mem_corr      : std_logic_vector((BL_MEM_DAT-1) downto 0); -- 
  signal   mem_ecc       : std_logic_vector((BL_MEM_ECC-1) downto 0); -- 
  signal   flag_rdy      : std_logic; -- 
  signal   flag_again    : std_logic; -- 
  signal   update_mem    : std_logic; -- 
  constant MEM_DEFAULT   : std_logic_vector((BL_MEM_DAT-1) downto 0) := (others => '0');
  
  -- ECC
  signal flag_ecc_err    : std_logic;
  signal flag_ecc_fail   : std_logic;
  
  -- NVM Read
  signal nvm_err         : std_logic;
  signal nvm_1bit_err    : std_logic;
  signal nvm_2bit_err    : std_logic;
  
  constant BL_FAIL_CNT   : integer := 2;
  signal   fail_cnt      : unsigned((BL_FAIL_CNT-1) downto 0); -- Counter for Fail Read
  constant VAL_FAIL_MAX  : unsigned((BL_FAIL_CNT-1) downto 0) := "10"; -- 
  
  -- NVM ip_bus
  signal en_rd           : std_logic;
  
  -- << MEM_FSM >>
 type mem_ctrl_state is (
    ST0_RESET,         -- 1   Reset
    ST1_IDLE,          -- 2   Idle
    ST2_READ_POINTER,  -- 3   Read Pointer Location 3 Words from OTP
    ST3_CALC_BLK,      -- 4   Calculate Current OTP Block
    ST4_READ_BLK,      -- 5   Read OTP 15 Words - Data from Block
    ST5_READ_ECC,      -- 6   Read OTP 1 Word - ECC from Block
    ST6_CHK_ECC        -- 7   Check Data + ECC
  );
  signal MEM_STATE  : mem_ctrl_state;  -- memory control state
  signal NXT_STATE  : mem_ctrl_state;  -- next state
  
  signal set_otp_slp         : std_logic;
  signal flag_rdy_pointer    : std_logic;
  signal en_read_pointer     : std_logic;
  signal str_read_pointer    : std_logic;
  signal flag_valid_pointer  : std_logic;
  signal str_calc_block      : std_logic;
  signal en_calc_block       : std_logic;
  signal str_read_block      : std_logic;
  signal en_read_words       : std_logic;
  signal str_read_ecc        : std_logic;
  signal en_read_ecc         : std_logic;
  signal en_latch_corr       : std_logic;
  
begin  -- MEM_CTRL_RTL
  
  ---------------------------------------------------
  -- outputs
  ---------------------------------------------------
  o_sleep_mode  <= otp_slp;
  o_nvm_err     <= nvm_err;
  o_rdy_mem     <= flag_rdy;
  o_ecc_err     <= nvm_1bit_err;
  o_ecc_fail    <= nvm_2bit_err;
  o_data        <= mem_dat;
  
  ---------------------------------------------------
  -- inputs
  ---------------------------------------------------
  otp_hold    <= '1' when ((i_ip_bus.ack = '0') and (en_rd = '1'))
  else           '0';
  otp_dr      <= i_ip_bus.dat;
  wait_latch  <= '1' when ((otp_hold = '1') and (en_rd = '1'))
  else           '1' when (en_rd = '0')
  else           '0';
  
  update_mem  <= i_update_mem or flag_again;
  
  ---------------------------------------------------
  -- bypass - DUMMY
  ---------------------------------------------------
  o_jtag_bus   <= i_jtag_bus;
  
  ---------------------------------------------------
  -- ip_bus - 
  ---------------------------------------------------
  o_ip_bus.dat  <= (others => '0');
  o_ip_bus.adr  <= otp_addr;
  o_ip_bus.we   <= '0';            -- Read Only
  o_ip_bus.sel  <= "00";           -- unused
  o_ip_bus.stb  <= active_read;
  o_ip_bus.ack  <= '0';
  
  en_rd         <= '1' when (active_read = '1')
  else             '0';
  
  ---------------------------------------------------------
  -- Pointer Counter - Read
  ---------------------------------------------------------
  pointer_cnt_ctrl : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      ptr_cnt  <= (others => '1');
    elsif rising_edge(i_sys_clk) then
      if (str_read_pointer = '1') then
        ptr_cnt  <= (others => '0');
      elsif (wait_latch = '1') then
        ptr_cnt  <= ptr_cnt;
      elsif (en_read_pointer = '1') then
        ptr_cnt  <= ptr_cnt + 1;
      end if;
    end if;
  end process pointer_cnt_ctrl;
  
  flag_rdy_pointer  <= '1' when (ptr_cnt >= VAL_PTR_MAX) else '0';
  
  ---------------------------------------------------------
  -- Pointer - Data Latch
  ---------------------------------------------------------
  pointer_data_ctrl : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      otp_ptr0   <= (others => '0');
      otp_ptr1   <= (others => '0');
      otp_ptr2   <= (others => '0');
      valid_ptr  <= (others => '0');
    elsif rising_edge(i_sys_clk) then
      -------------------------------------------------------------------------
      if (str_read_pointer = '1') then
        otp_ptr0      <= (others => '0');
        valid_ptr(0)  <= '0';
      elsif (otp_hold = '0') and (en_read_pointer = '1') and (ptr_cnt = "00") then
        otp_ptr0      <= otp_dr;
        valid_ptr(0)  <= '1';
      end if;
      -------------------------------------------------------------------------
      if (str_read_pointer = '1') then
        otp_ptr1      <= (others => '0');
        valid_ptr(1)  <= '0';
      elsif (otp_hold = '0') and (en_read_pointer = '1') and (ptr_cnt = "01") then
        otp_ptr1      <= otp_dr;
        valid_ptr(1)  <= '1';
      end if;
      -------------------------------------------------------------------------
      if (str_read_pointer = '1') then
        otp_ptr2      <= (others => '0');
        valid_ptr(2)  <= '0';
      elsif (otp_hold = '0') and (en_read_pointer = '1') and (ptr_cnt = "10") then
        otp_ptr2      <= otp_dr;
        valid_ptr(2)  <= '1';
      end if;
      -------------------------------------------------------------------------
    end if;
  end process pointer_data_ctrl;
  
  flag_valid_pointer  <= '1' when (valid_ptr = "111")
  else                   '0';
  
  -------------------------------------------------------------------------
  -- blk_cnt
  -- 0000       - initial, Can be Empty otp_ptr_i=000 (should be otp_ptr_i=111)
  -- 0001       - Block01 (should be otp_ptr_i=000) Stop
  -- 0010       - Block02 
  -- 1100       - Block12, No Real Data so Auto-Stop
  -------------------------------------------------------------------------
  pointer_bit_ctrl : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      blk_cnt        <= (others => '0');
      valid_ptr_bit  <= '0';
      err_ptr_bit    <= '0';
      err_ptr_empty  <= '0';
    elsif rising_edge(i_sys_clk) then
      if (str_calc_block = '1') then                                                                                        -- Start of Pointers processing
        blk_cnt        <= (others => '0');
        valid_ptr_bit  <= '0';
        err_ptr_bit    <= '0';
        err_ptr_empty  <= '0';
      elsif (en_calc_block = '1') and (blk_cnt = VAL_BLK_ZERO) and (flag_blk_empty = '1') and (flag_ptr_err0 = '1') then    -- Empty Array (Pointer_0=000) + '1' value error
        err_ptr_empty  <= '1';
        err_ptr_bit    <= '1';
      elsif (en_calc_block = '1') and (blk_cnt = VAL_BLK_ZERO) and (flag_blk_empty = '1') then                              -- Empty Array (Pointer_0=000)
        err_ptr_empty  <= '1';
      elsif (en_calc_block = '1') and (flag_blk_full = '1') and (blk_cnt >= VAL_BLK_MAX) and (flag_ptr_err1 = '1') then     -- Last Pointer Full (Pointer_11=111) + '0' value error / Stop
        blk_cnt        <= blk_cnt + 1;
        err_ptr_bit    <= '1';
        valid_ptr_bit  <= '1';
      elsif (en_calc_block = '1') and (flag_blk_full = '1') and (blk_cnt >= VAL_BLK_MAX) then                               -- Last Pointer Full (Pointer_11=111) / Stop
        blk_cnt        <= blk_cnt + 1;
        valid_ptr_bit  <= '1';
      elsif (en_calc_block = '1') and (flag_blk_full = '1') and (flag_ptr_err1 = '1') then                                  -- Current Pointer Full (Pointer_i=111) + '0' value error / Next
        blk_cnt        <= blk_cnt + 1;
        err_ptr_bit    <= '1';
      elsif (en_calc_block = '1') and (flag_blk_full = '1') then                                                            -- Current Pointer Full (Pointer_i=111) / Next
        blk_cnt        <= blk_cnt + 1;
      elsif (en_calc_block = '1') and (flag_blk_empty = '1') and (flag_ptr_err0 = '1') then                                 -- Current Pointer Empty (Pointer_i=000) + '1' value error / Stop
        blk_cnt        <= blk_cnt;
        valid_ptr_bit  <= '1';
        err_ptr_bit    <= '1';
      elsif (en_calc_block = '1') and (flag_blk_empty = '1') then                                                           -- Current Pointer Empty (Pointer_i=000) / Stop
        blk_cnt        <= blk_cnt;
        valid_ptr_bit  <= '1';
      end if;
    end if;
  end process pointer_bit_ctrl;
  
  flag_blk_empty  <= '0' when (blk_cnt > VAL_BLK_MAX)
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '0') and (otp_ptr1(to_integer(blk_cnt)) = '0') and (otp_ptr2(to_integer(blk_cnt)) = '0')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '1') and (otp_ptr1(to_integer(blk_cnt)) = '0') and (otp_ptr2(to_integer(blk_cnt)) = '0')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '0') and (otp_ptr1(to_integer(blk_cnt)) = '1') and (otp_ptr2(to_integer(blk_cnt)) = '0')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '0') and (otp_ptr1(to_integer(blk_cnt)) = '0') and (otp_ptr2(to_integer(blk_cnt)) = '1')
  else               '0';
  
  flag_blk_full   <= '0' when (blk_cnt > VAL_BLK_MAX)
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '1') and (otp_ptr1(to_integer(blk_cnt)) = '1') and (otp_ptr2(to_integer(blk_cnt)) = '1')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '1') and (otp_ptr1(to_integer(blk_cnt)) = '1') and (otp_ptr2(to_integer(blk_cnt)) = '0')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '1') and (otp_ptr1(to_integer(blk_cnt)) = '0') and (otp_ptr2(to_integer(blk_cnt)) = '1')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '0') and (otp_ptr1(to_integer(blk_cnt)) = '1') and (otp_ptr2(to_integer(blk_cnt)) = '1')
  else               '0';
  
  flag_ptr_err0   <= '0' when (blk_cnt > VAL_BLK_MAX)
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '1') and (otp_ptr1(to_integer(blk_cnt)) = '0') and (otp_ptr2(to_integer(blk_cnt)) = '0')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '0') and (otp_ptr1(to_integer(blk_cnt)) = '1') and (otp_ptr2(to_integer(blk_cnt)) = '0')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '0') and (otp_ptr1(to_integer(blk_cnt)) = '0') and (otp_ptr2(to_integer(blk_cnt)) = '1')
  else               '0';
  
  flag_ptr_err1   <= '0' when (blk_cnt > VAL_BLK_MAX)
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '1') and (otp_ptr1(to_integer(blk_cnt)) = '1') and (otp_ptr2(to_integer(blk_cnt)) = '0')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '1') and (otp_ptr1(to_integer(blk_cnt)) = '0') and (otp_ptr2(to_integer(blk_cnt)) = '1')
  else               '1' when (otp_ptr0(to_integer(blk_cnt)) = '0') and (otp_ptr1(to_integer(blk_cnt)) = '1') and (otp_ptr2(to_integer(blk_cnt)) = '1')
  else               '0';
  
  ---------------------------------------------------------
  -- Block Counter - Read
  ---------------------------------------------------------
  block_cnt_ctrl : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      blk_word        <= (others => '1');
      flag_rdy_words  <= '0';
      flag_rdy_ecc    <= '0';
    elsif rising_edge(i_sys_clk) then
      ----------------------------------
      if (str_read_block = '1') then
        blk_word        <= (others => '0');
        flag_rdy_words  <= '0';
      elsif (wait_latch = '1') then
        null;
      elsif (en_read_words = '1') and (flag_last_word = '1') then
        flag_rdy_words  <= '1';
      elsif (en_read_words = '1') then
        blk_word  <= blk_word + 1;
      end if;
      ----------------------------------
      if (str_read_ecc = '1') then
        flag_rdy_ecc   <= '0';
      elsif (wait_latch = '1') then
        null;
      elsif (en_read_ecc = '1') then
        flag_rdy_ecc   <= '1';
      end if;
      ----------------------------------
    end if;
  end process block_cnt_ctrl;
  
  flag_last_word  <= '1' when (blk_word >= VAL_WORD_MAX) else '0';
  
  ---------------------------------------------------------
  -- Memory Registers
  ---------------------------------------------------------
  memory_regs_ctrl : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      mem_dat     <= MEM_DEFAULT;
      mem_ecc     <= (others => '0');
      flag_rdy    <= '0';
      flag_again  <= '0';
    elsif rising_edge(i_sys_clk) then
      if (update_mem = '1') then
        flag_rdy    <= '0';
        flag_again  <= '0';
      elsif (en_latch_corr = '1') and (flag_ecc_fail = '1') and (fail_cnt >= VAL_FAIL_MAX) then
        mem_dat     <= MEM_DEFAULT;
        flag_rdy    <= '1';
      elsif (en_latch_corr = '1') and (flag_ecc_fail = '1') then
        flag_rdy    <= '0';
        flag_again  <= '1';
      elsif (en_latch_corr = '1') then --(flag_ecc_fail = '0')
        mem_dat     <= mem_corr;
        flag_rdy    <= '1';
      elsif (wait_latch = '1') then
        null;
      elsif (en_read_words = '1') then
      --mem_dat((to_integer(blk_word)*12 + 11) downto (to_integer(blk_word)*12))  <= otp_dr(11 downto 0);
        case to_integer(blk_word) is
        when  0     => mem_dat( 11 downto   0)  <= otp_dr(11 downto 0);
        when  1     => mem_dat( 23 downto  12)  <= otp_dr(11 downto 0);
        when  2     => mem_dat( 35 downto  24)  <= otp_dr(11 downto 0);
        when  3     => mem_dat( 47 downto  36)  <= otp_dr(11 downto 0);
        when  4     => mem_dat( 59 downto  48)  <= otp_dr(11 downto 0);
        when  5     => mem_dat( 71 downto  60)  <= otp_dr(11 downto 0);
        when  6     => mem_dat( 83 downto  72)  <= otp_dr(11 downto 0);
        when  7     => mem_dat( 95 downto  84)  <= otp_dr(11 downto 0);
        when  8     => mem_dat(107 downto  96)  <= otp_dr(11 downto 0);
        when  9     => mem_dat(119 downto 108)  <= otp_dr(11 downto 0);
        when 10     => mem_dat(131 downto 120)  <= otp_dr(11 downto 0);
        when 11     => mem_dat(143 downto 132)  <= otp_dr(11 downto 0);
        when 12     => mem_dat(155 downto 144)  <= otp_dr(11 downto 0);
        when 13     => mem_dat(167 downto 156)  <= otp_dr(11 downto 0);
        when others => mem_dat(179 downto 168)  <= otp_dr(11 downto 0);
        end case;
      elsif (en_read_ecc = '1') then
        mem_ecc   <= otp_dr(11 downto 0);
      end if;
    end if;
  end process memory_regs_ctrl;
  
  ---------------------------------------------------------
  -- ECC/NVM Error Flags
  ---------------------------------------------------------
  nvm_err_ctrl : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      fail_cnt      <= (others => '0');
      nvm_err       <= '0';
      nvm_1bit_err  <= '0';
      nvm_2bit_err  <= '0';
    elsif rising_edge(i_sys_clk) then
      if (update_mem = '1') and (fail_cnt < VAL_FAIL_MAX) then
        nvm_err       <= '0';
      elsif (en_latch_corr = '1') and (flag_ecc_fail = '1') and (fail_cnt < VAL_FAIL_MAX) then
        fail_cnt  <= fail_cnt + 1;
      elsif (en_latch_corr = '1') and (flag_ecc_fail = '1') and (fail_cnt >= VAL_FAIL_MAX) then
        nvm_err  <= '1';
      end if;
      
      if (update_mem = '1') then
        nvm_1bit_err  <= '0';
      elsif (en_latch_corr = '1') and (flag_ecc_err = '1') then
        nvm_1bit_err  <= '1';
      end if;
      
      if (update_mem = '1') then
        nvm_2bit_err  <= '0';
      elsif (en_latch_corr = '1') and (flag_ecc_fail = '1') then
        nvm_2bit_err  <= '1';
      end if;
    end if;
  end process nvm_err_ctrl;
  
  ---------------------------------------------------------
  -- OTP Inputs Control
  ---------------------------------------------------------
  otp_array_sleep : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      otp_slp  <= '1';
    elsif rising_edge(i_sys_clk) then
      if (set_otp_slp = '1') then
        otp_slp  <= '1';
      else
        otp_slp  <= '0';
      end if;
    end if;
  end process otp_array_sleep;
  
  -- otp_array_address : process (i_rst_n, i_sys_clk) is begin
    -- if (i_rst_n = '0') then
      -- otp_addr    <= (others => '0');
    -- elsif rising_edge(i_sys_clk) then
      -- if (en_read_pointer = '1') then
        -- otp_addr  <= fill_addr_ptr & std_logic_vector(ptr_cnt);
      -- elsif (en_read_words = '1') then
        -- otp_addr  <= fill_addr_blk & std_logic_vector(blk_cnt) & std_logic_vector(blk_word);
      -- elsif (en_read_ecc = '1') then
        -- otp_addr  <= fill_addr_blk & std_logic_vector(blk_cnt) & ADDR_ECC;
      -- else
        -- null;
      -- end if;
    -- end if;
  -- end process otp_array_address;
  
  otp_array_address : process (en_read_pointer, en_read_words, en_read_ecc, ptr_cnt, blk_cnt, blk_word) is begin
    if (en_read_pointer = '1') then
      otp_addr  <= fill_addr_ptr & std_logic_vector(ptr_cnt);
    elsif (en_read_words = '1') then
      otp_addr  <= fill_addr_blk & std_logic_vector(blk_cnt) & std_logic_vector(blk_word);
    elsif (en_read_ecc = '1') then
      otp_addr  <= fill_addr_blk & std_logic_vector(blk_cnt) & ADDR_ECC;
    else
      otp_addr    <= (others => '0');
    end if;
  end process otp_array_address;
  
  otp_read_active : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      active_read  <= '0';
    elsif rising_edge(i_sys_clk) then
      if    (NXT_STATE = ST2_READ_POINTER) and not ((ptr_cnt = 2) and (otp_hold = '0')) then
        active_read  <= '1';
      elsif (NXT_STATE = ST4_READ_BLK) then
        active_read  <= '1';
      elsif (NXT_STATE = ST5_READ_ECC) and (MEM_STATE = ST4_READ_BLK) then
        active_read  <= '1';
      elsif (NXT_STATE = ST5_READ_ECC) and not (otp_hold = '0') then
        active_read  <= '1';
      else
        active_read  <= '0';
      end if;
    end if;
  end process otp_read_active;
  
  -- FSM: 
  ---------------------------------------------------------
  -- state register
  ---------------------------------------------------------
  state_process : process (i_rst_n, i_sys_clk) is begin
    if (i_rst_n = '0') then
      MEM_STATE <= ST0_RESET;
    elsif rising_edge(i_sys_clk) then
      MEM_STATE <= NXT_STATE;
    end if;
  end process state_process;
  
  fsm_process : process (MEM_STATE, i_off_mem, update_mem, flag_rdy_pointer, flag_valid_pointer, err_ptr_empty, flag_rdy_words, flag_rdy_ecc,
                         valid_ptr_bit, flag_rdy, flag_again, nvm_2bit_err, nvm_err) is begin
    ------------------------------------ 
    set_otp_slp        <= '0';
    en_read_pointer    <= '0';
    str_read_pointer   <= '0';
    str_calc_block     <= '0';
    en_calc_block      <= '0';
    str_read_block     <= '0';
    en_read_words      <= '0';
    str_read_ecc       <= '0';
    en_read_ecc        <= '0';
    en_latch_corr      <= '0';
    --
    -- (i_sys_state = c_sys_power_off) "000001"
    -- (i_sys_state = c_sys_wake_up)   "000010"
    -- (i_sys_state = c_sys_initial)   "000100"
    -- (i_sys_state = c_sys_normal)    "001000"
    -- (i_sys_state = c_sys_scrap)     "010000"
    -- (i_sys_state = c_sys_mcu_res)   "100000"
    ------------------------------------ 
    case (MEM_STATE) is
      when ST1_IDLE =>
        if (i_off_mem = '1') then
          NXT_STATE          <= ST0_RESET;
          set_otp_slp        <= '1';
        elsif (update_mem = '1') then
          NXT_STATE          <= ST2_READ_POINTER;
          str_read_pointer   <= '1';
        else
          NXT_STATE          <= ST1_IDLE;
        end if; 
      when ST2_READ_POINTER =>
        if (i_off_mem = '1') then
          NXT_STATE          <= ST0_RESET;
          set_otp_slp        <= '1';
        elsif (flag_rdy_pointer = '1') and (flag_valid_pointer = '1') then
          NXT_STATE          <= ST3_CALC_BLK;
          str_calc_block     <= '1';
        elsif (flag_rdy_pointer = '1') then -- (flag_valid_pointer = '0')
          NXT_STATE          <= ST1_IDLE;
--        set_fsm_error      <= '1';                                                                              -- TODO
        else
          en_read_pointer    <= '1';
          NXT_STATE          <= ST2_READ_POINTER;
        end if;
       when ST3_CALC_BLK =>
        if (i_off_mem = '1') then
          NXT_STATE          <= ST0_RESET;
          set_otp_slp        <= '1';
        elsif (err_ptr_empty = '1') then
          NXT_STATE          <= ST1_IDLE;
--        set_fsm_error      <= '1';                                                                              -- TODO
        elsif (valid_ptr_bit = '1') then
          NXT_STATE          <= ST4_READ_BLK;
          str_read_block     <= '1';
        else
          NXT_STATE          <= ST3_CALC_BLK;
          en_calc_block      <= '1';
        end if;
       when ST4_READ_BLK =>
        if (i_off_mem = '1') then
          NXT_STATE          <= ST0_RESET;
          set_otp_slp        <= '1';
        elsif (flag_rdy_words = '1') then
          NXT_STATE          <= ST5_READ_ECC;
          str_read_ecc       <= '1';
          en_read_ecc        <= '1';
        else
          NXT_STATE          <= ST4_READ_BLK;
          en_read_words      <= '1';
        end if;
      when ST5_READ_ECC =>
        if (i_off_mem = '1') then
          NXT_STATE          <= ST0_RESET;
          set_otp_slp        <= '1';
        elsif (flag_rdy_ecc = '1') then
          NXT_STATE          <= ST6_CHK_ECC;
          en_latch_corr      <= '1';
        else
          NXT_STATE          <= ST5_READ_ECC;
          en_read_ecc        <= '1';
        end if;
      when ST6_CHK_ECC =>
        if (i_off_mem = '1') then
          NXT_STATE          <= ST0_RESET;
          set_otp_slp        <= '1';
        elsif (flag_again = '1') and (nvm_2bit_err = '1') and (fail_cnt <= VAL_FAIL_MAX) then
          NXT_STATE          <= ST2_READ_POINTER;
          str_read_pointer   <= '1';
        elsif (flag_rdy = '1') and (nvm_2bit_err = '1') then
          NXT_STATE          <= ST1_IDLE;
        elsif (flag_rdy = '1') then -- (nvm_2bit_err = '0')
          NXT_STATE          <= ST1_IDLE;
        else
          NXT_STATE          <= ST6_CHK_ECC;
        end if;
      when others  =>  -- ST0_RESET
        if (i_off_mem = '0') then
          NXT_STATE          <= ST1_IDLE;
        else
          set_otp_slp        <= '1';
          NXT_STATE          <= ST0_RESET;
        end if; 
    end case;
  end process fsm_process;
  
  -------------------------------------------------------------------------------
  -- subblocks instantiations
  -------------------------------------------------------------------------------
  DW_ECC_snps: if (target_technology_TSMC = true) generate
  u_decoder_ecc: DW_ecc 
  generic map(
    width    => BL_MEM_DAT,
    chkbits  => BL_MEM_ECC,
    synd_sel => 0
  )
  port map(
    correct_n  => '0',                   -- ecc_off ?
    gen        => '0',                   -- read only
    datain     => mem_dat,
    chkin      => mem_ecc,
    dataout    => mem_corr,              -- Initial or Corrected Data
    chkout     => open,                  -- ECC syndrome (synd_sel=1)
    err_detect => flag_ecc_err,          -- Error has been detected / corrected
    err_multpl => flag_ecc_fail          -- Uncorrected Error
  );
  end generate DW_ECC_snps;

  DW_ECC_fpga: if (target_technology_FPGA = true) generate
    begin
    mem_corr <= mem_dat;
    flag_ecc_err <= '0';
    flag_ecc_fail <= '0';
  end generate DW_ECC_fpga;
  -------------------------------------------------------------------------------
end MEM_CTRL_RTL;
