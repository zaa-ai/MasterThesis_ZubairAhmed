-------------------------------------------------------------------------------
-- Title       : package for OTP_WRAPPER module
-- Project     : E13707 Airbag
-------------------------------------------------------------------------------
-- File        : otp_wrapper_pkg.vhd
-- Author      : Ivonne Pera (IME) ELDO
--               Denis Poliakov (DPOL) ELSPB
-- Company     : ELMOS Semiconductor AG
-- Created     : 10.06.2016
-- Last update : 06.06.2017
-------------------------------------------------------------------------------
-- Copyright (c) 2016
-------------------------------------------------------------------------------
-- Revisions  :
-- Date        Version  Author  Description
-- 10.06.2016   1.0     dpol    Created
-- 08.07.2016   1.1     dpol    c_block_addr_otp_eccctrl_lsb, c_block_addr_otp_eccctrl_msb added
--                              c_block_addr_otp_cr_lsb, c_block_addr_otp_cr_msb added
-- 21.07.2016   1.2     dpol    control and data buses implemented for interface
-- 25.07.2016   1.3     dpol    c_otp_trp_dat added, BIT_EN_BIST added
-- 02.08.2016   1.4     dpol    BIT_EN_BIST removed, 
--                              BIT_OTP_PROG renamed to BIT_OTP_PGM
-- 11.08.2016   1.5     dpol    System Address shifted to address_map_pkg.vhd
-- 23.09.2016   1.6     dpol    c_instr_sfr_sysmode added
-- 16.11.2016   1.7     dpol    BL_OTPBISTCTRL changed from 12bit to 16bit
--                              BL_MAX_SOAK, BIT_MAX_SOAK_LSB, BIT_MAX_SOAK_MSB added
-- 17.11.2016   1.8     dpol    BIT_BYPASS added
--                              BL_OTPBISTCONF changed from 12bit to 16bit
--                              BIT_ECCERR_L_LSB, BIT_ECCERR_L_MSB added
--                              BIT_ECCERR_H_LSB, BIT_ECCERR_H_MSB added
-- 25.11.2016   1.9     dpol    JTAG IR changed from 0x68:0x70 to 0xA0:0xA8
-- 06.06.2017   1.10    dpol    c_otp_wl_dat=c_otp_wl_word=12
--                              OTP12/OTP32 -> OTP
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

package otp_wrapper_pkg is

  constant c_otp_vrr_dat   : std_logic_vector(3 downto 0) := "0100";
  
  
  -- OTP JTAG instructions
  constant c_instr_otp_write_ctrl      : integer := 16#A0#;
  constant c_instr_otp_write_conf      : integer := 16#A1#;
  constant c_instr_otp_write           : integer := 16#A2#;  -- write full Array
  constant c_instr_otp_write_ecc       : integer := 16#A3#;  -- write with ECC encoding
  constant c_instr_otp_read            : integer := 16#A4#;  -- read full Array
  constant c_instr_otp_read_ecc        : integer := 16#A5#;  -- read with ECC decoding
  constant c_instr_otpbist_ctrl        : integer := 16#A6#;
  constant c_instr_otpbist_conf        : integer := 16#A7#;
  constant c_instr_otpbist_stat        : integer := 16#A8#;
  constant c_instr_otp_write_pulse_conf: integer := 16#A9#;
  
  
  constant c_instr_sfr_sysmode         : integer := 16#C1#; -- application specific JTAG IR : OTP sleep mode
  
  constant c_otp_array_size : integer := 4096; -- OTP array size
  constant c_otp_wl_adr     : integer := 12;   -- OTP address width
  constant c_otp_wl_dat     : integer := 12;   -- OTP data width
  constant c_otp_wl_ecc     : integer :=  0;   -- OTP data ecc width
  constant c_otp_wl_word    : integer := 12;   -- OTP word width (data + ecc)
  constant c_otp_wl_ctrl    : integer := 16;   -- OTP control register width
  constant c_otp_cpu_dat    : integer :=  8;   -- cpu data width
  constant c_otp_prog_key   : std_logic_vector (31 downto 0) := x"84913BAC";  -- access key for programming
  
  constant c_otp_wl_mpp     : integer :=  8;   -- MPP[]
  constant c_otp_wl_mrr     : integer := 16;   -- MRR[]
  constant c_otp_wl_mr      : integer :=  8;   -- MR[]
  
  constant c_otp_trp_dat    : integer :=  7;   -- TRP
  
  -- OTP control register description
  constant BL_OTPCTRL      : integer := 16; -- c_otp_wl_ctrl
  constant BL_OTP_MON      : integer :=  2;
  
  constant BIT_EN_AUTO     : integer :=  0;
  constant BIT_EN_OTPCP    : integer :=  1;
  constant BIT_EN_VPP      : integer :=  2;
  constant BIT_OTP_CTRL3   : integer :=  3; -- was BIT_EN_BIST
  constant BIT_EN_OTP      : integer :=  4;
  constant BIT_OTP_CTRL5   : integer :=  5; -- reserved
  constant BIT_SEL_OTP     : integer :=  6;
  constant BIT_OTP_CTRL7   : integer :=  7; -- reserved
  constant BIT_CTRL_CLK    : integer :=  8;
  constant BIT_CTRL_WE     : integer :=  9;
  constant BIT_OTP_MON_LSB : integer := 10;
  constant BIT_OTP_MON_MSB : integer := 11;
  constant BIT_AUTOINC     : integer := 12;
  constant BIT_BYPASS      : integer := 13;
  constant BIT_OTP_CTRL14  : integer := 14; -- reserved
  constant BIT_OTP_CTRL15  : integer := 15; -- reserved
  
  -- OTP Config Register description
  constant BL_OTP_CONF     : integer := 32;
  constant BL_OTP_MPP      : integer :=  8;
  constant BL_OTP_MRR      : integer := 16;
  constant BL_OTP_MR       : integer :=  8;
  constant BIT_OTP_MPP_LSB : integer :=  0;
  constant BIT_OTP_MPP_MSB : integer :=  7;
  constant BIT_OTP_MRR_LSB : integer :=  8;
  constant BIT_OTP_MRR_MSB : integer := 23;
  constant BIT_OTP_MR_LSB  : integer := 24;
  constant BIT_OTP_MR_MSB  : integer := 31;
  
  -- OTP Write config register description
  constant BL_OTP_WRITE_CONFIG : integer := 12;
  constant BIT_OTP_WRITE_CONFIG_MSB : integer := BL_OTP_WRITE_CONFIG-1;
  constant BIT_OTP_WRITE_CONFIG_LSB : integer := 0;
  
  -- OTP BIST Control Register IR=0x6E (16bit)
  constant BL_OTPBISTCTRL   : integer := 16;
  constant BL_MAX_SOAK      : integer :=  3;
  constant BIT_OTP_PGM      : integer :=  0;
  constant BIT_OTP_READ     : integer :=  1;
  constant BIT_SOAK         : integer :=  2;
  constant BIT_BIST_CTRL3   : integer :=  3; -- reserved
  constant BIT_EN_SOAK      : integer :=  4;
  constant BIT_STRESS       : integer :=  5;
  constant BIT_SEL_TRP      : integer :=  6;
  constant BIT_SEL_RD       : integer :=  7;
  constant BIT_SEL_MPP      : integer :=  8;
  constant BIT_SEL_MRR      : integer :=  9;
  constant BIT_SEL_MR       : integer := 10;
  constant BIT_BIST_CTRL11  : integer := 11; -- reserved
  constant BIT_MAX_SOAK_LSB : integer := 12;
  constant BIT_MAX_SOAK_MSB : integer := 14;
  constant BIT_BIST_CTRL15  : integer := 15; -- reserved
  
  -- OTP BIST/TEST Config Register IR=0x6F (16bit)
  constant BL_OTPBISTCONF   : integer := 16;
  constant BL_TRP           : integer :=  7;
  constant BL_RD_MODE       : integer :=  2;
  constant BL_ECCERR_L      : integer :=  2;
  constant BL_ECCERR_H      : integer :=  2;
  constant BIT_TRP_LSB      : integer :=  0;
  constant BIT_TRP_MSB      : integer :=  6;
  constant BIT_BIST_CONF7   : integer :=  7;
  constant BIT_RD_MODE_LSB  : integer :=  8;
  constant BIT_RD_MODE_MSB  : integer :=  9;
  constant BIT_BIST_CONF10  : integer := 10; -- reserved
  constant BIT_BIST_CONF11  : integer := 11; -- reserved
  constant BIT_ECCERR_L_LSB : integer := 12;
  constant BIT_ECCERR_L_MSB : integer := 13;
  constant BIT_ECCERR_H_LSB : integer := 14;
  constant BIT_ECCERR_H_MSB : integer := 15;
  
  -- OTP BIST Status Register IR=0x70 (16 bit)
  constant BL_OTPBISTSTAT      : integer := 16;
  constant BL_PROG_BIT         : integer :=  6;
  constant BL_SOAK_PULSE       : integer :=  4;
  constant BIT_PROG_BIT_LSB    : integer :=  0;
  constant BIT_PROG_BIT_MSB    : integer :=  5;
  constant BIT_BIST_STAT6      : integer :=  6;
  constant BIT_DONE            : integer :=  7;
  constant BIT_SOAK_PULSE_LSB  : integer :=  8;
  constant BIT_SOAK_PULSE_MSB  : integer := 11;
  constant BIT_BUSY            : integer := 12;
  constant BIT_FAIL0           : integer := 13;
  constant BIT_FAIL1           : integer := 14;
  constant BIT_SOAK_STAT       : integer := 15;
  
  
  -------------------------------------------------------------------------------
  -- Memory Bus Naming :
  -- memory  short  control data
  -- name    name   bus     dus
  -- RAM     RA     cra     dra
  -- ROM     RO     cro     dro
  -- FLASH   FL     cfl     dfl
  -- EEPROM  EE     cee     dee
  -- OTP     OT     cot     dot
  -- MTP     MT     cmt     dmt
  -- Charge  CP     ccp     dcp
  -- Pump
  -------------------------------------------------------------------------------
  type t_cot_bus is record
    ehv   : std_logic;                                  -- Ative mode for OTP : on high-voltage READ and PROG
    oe    : std_logic;                                  -- Output enable
    sel   : std_logic;                                  -- OTP select
    we    : std_logic;                                  -- 
    ck    : std_logic;                                  -- Address/Data/Command Strobe
    mr    : std_logic_vector(c_otp_wl_mr-1 downto 0);   -- Read and Test mode control pins
    addr  : std_logic_vector(c_otp_wl_adr-1 downto 0);  -- address
  end record;
  
  type t_dot_bus is record
    data  : std_logic_vector(c_otp_wl_word-1 downto 0);  -- data read/write 32bit
  end record;
  
  type t_ccp_bus is record
    vppen     : std_logic;                                  -- Enable the VPP limiter and VPP charge pump
    vrren     : std_logic;                                  -- Enable the VRR generator, bandgap, bandgap bias, and buffer
    mpp       : std_logic_vector(c_otp_wl_mpp-1 downto 0);  -- Charge-Pump mode control
    mrr       : std_logic_vector(c_otp_wl_mrr-1 downto 0);  -- Read Voltage Regulator mode control
  end record;
  
  type t_dcp_bus is record
    clkout    : std_logic;                                  -- Buffered clock from VPP generator
    ppclkout  : std_logic;                                  -- internal oscillator output
  end record;
  
  -------------------------------------------------------------------------------
  -- CPU OTP + CTRL addresses range
  -------------------------------------------------------------------------------
  -- link to pkg_address_map.vhd is used
  -------------------------------------------------------------------------------
--constant c_block_addr_otp_bgn          : integer := c_addr_otp_bgn;      -- OTP array first (begin) address
--constant c_block_addr_otp_end          : integer := c_addr_otp_end;      -- OTP array last (end) address
--constant c_block_addr_otp_cr           : integer := c_addr_otp_cr;       -- OTP Control Register
--constant c_block_addr_otp_cr_lsb       : integer := c_addr_otp_cr_lsb;   -- OTP Control Register
--constant c_block_addr_otp_cr_msb       : integer := c_addr_otp_cr_msb;   -- OTP Control Register
--constant c_block_addr_otp_eccctrl      : integer := c_addr_otp_ecr;      -- OTP ECC Control Register
--constant c_block_addr_otp_eccctrl_lsb  : integer := c_addr_otp_ecr_lsb;  -- OTP ECC Control Register
--constant c_block_addr_otp_eccctrl_msb  : integer := c_addr_otp_ecr_msb;  -- OTP ECC Control Register
  
--constant c_block_addr_otp_bctrl_lsb    : integer := c_addr_otp_bctrl_lsb;   -- OTP BIST Control Register
--constant c_block_addr_otp_bctrl_msb    : integer := c_addr_otp_bctrl_msb;   -- OTP BIST Control Register
--constant c_block_addr_otp_bconf_lsb    : integer := c_addr_otp_bconf_lsb;   -- OTP BIST Config Register
--constant c_block_addr_otp_bconf_msb    : integer := c_addr_otp_bconf_msb;   -- OTP BIST Config Register
--constant c_block_addr_otp_bstat_lsb    : integer := c_addr_otp_bstat_lsb;   -- OTP BIST Status Register
--constant c_block_addr_otp_bstat_msb    : integer := c_addr_otp_bstat_msb;   -- OTP BIST Status Register
  
--constant c_block_addr_flash_key_ok  : integer := c_addr_flash_key_ok;  -- T.B.D.
--constant c_block_addr_flash_key1    : integer := c_addr_flash_key1;    -- T.B.D.
--constant c_block_addr_flash_key2    : integer := c_addr_flash_key2;    -- T.B.D.
--constant c_block_addr_flash_key3    : integer := c_addr_flash_key3;    -- T.B.D.
--constant c_block_addr_flash_key4    : integer := c_addr_flash_key4;    -- T.B.D.
  
--constant c_otp_start_address_conf : integer := 16#4000#;
--constant c_otp_end_address_conf   : integer := 16#7fff#;
--constant c_otp_start_address_app  : integer := 16#8000#;
--constant c_otp_end_address_app    : integer := 16#bfff#;
--constant c_otp_end_address_app    : integer := 16#efff#;
--constant c_otp_cr_address         : integer := 16#301F#; -- was 16#0208#  DPOL
--constant c_otp_ecr_address        : integer := 16#3020#; -- was 16#0209# 05.12.2013 DPOL
--constant c_otp_key_ok_address     : integer := 16#3030#;
--constant c_otp_key1_address       : integer := 16#3031#;
--constant c_otp_key2_address       : integer := 16#3032#;
--constant c_otp_key3_address       : integer := 16#3033#;
--constant c_otp_key4_address       : integer := 16#3034#;
  
end otp_wrapper_pkg;
