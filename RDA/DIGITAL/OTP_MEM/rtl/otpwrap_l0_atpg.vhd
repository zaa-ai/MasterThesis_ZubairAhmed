-------------------------------------------------------------------------------
-- Title       : OTP WRAPPER LEVEL0
-- Project     : standard digital IP
-------------------------------------------------------------------------------
-- Description : direct access to OTP array
--               with ATPG gating
-------------------------------------------------------------------------------
-- Subblocks   : otp4kx12_cp pure_tinv
-------------------------------------------------------------------------------
-- File        : otpwrap_l0_atpg.vhd
-- Author      : Ivonne Pera (IME) ELDO
--               Denis Poliakov (DPOL) ELSPB
-- Company     : ELMOS Semiconductor AG
-- Created     : 02.06.2016
-- Last update : 06.06.2017
-------------------------------------------------------------------------------
-- Copyright (c) 2016 ELMOS Semiconductor AG
-------------------------------------------------------------------------------
-- Revisions   :
-- Date        Version  Author  Description
-- 02.06.2016   0.1     dpol    initial release for OTP4KX44_CP
-- 07.07.2016   0.2     dpol    High-Z state added, pure_and added
-- 21.07.2016   0.5     dpol    control and data buses implemented for interface
-- 10.08.2016   1.0     dpol    TINV added for High-Z state control
-- 11.08.2016   1.1     dpol    OTP4KX44_CP: added VPP & VREF
--                              a_otp_vpp, a_otp_vref added
-- 17.08.2016   1.2     mslz    pure_tinv IO names changed according to new pure-cell lib
-- 05.09.2016   1.3     dpol    TINV commented for EL3.5 system bus
-- 28.09.2016   1.4     ime     set OE to low during atpg_mode
--                              added VCC analog as input for IPS and VRR analog as output
-- 04.10.2016   1.5     dpol    a_otp_vrr output added
--                              a_otp_vpp renamed to a_otp_vpppad
--                              a_otp_vbg, a_otp_vpppad, a_otp_vref changed to output
-------------------------------------------------------------------------------
-- 17.04.2017   2.0     dpol    otp4kx44_cp changed to otp4kx12_cp
--                              32bit interface removed
-- 06.06.2017   2.1     dpol    12/32bit version, ATPG gating updated
-- 18.07.2017   2.2     dpol    otp_mrr&otp_mpp fully gated for ATPG
-- 11.01.2018   2.3     ime     deleted input a_otp_vcc
--                              set oe always to 1, no o_data_otp floating during iddq
--                              mask otp_mr during iddq to prevent current
-- 12.01.2018   2.4     dpol    ATPG bypass logic corrected
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

library OTP_MEM;
use OTP_MEM.otp_wrapper_pkg.all;

library digital;
use digital.digital_pkg.target_technology_TSMC;
use digital.digital_pkg.target_technology_FPGA;

entity otpwrap_l0_atpg is
  port(
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
end otpwrap_l0_atpg;

architecture RTL of otpwrap_l0_atpg is
  -------------------------------------------------------------------------------
  -- subblocks
  -------------------------------------------------------------------------------
  component otp4kx12_cp
  port (
    -- Charge-Pump Control
    VPPEN     : in  std_logic;                                  -- Enable the VPP limiter and VPP charge pump
    VRREN     : in  std_logic;                                  -- Enable the VRR generator, bandgap, bandgap bias, and buffer
    MPP       : in  std_logic_vector(c_otp_wl_mpp-1 downto 0);  -- Charge-Pump mode control
    MRR       : in  std_logic_vector(c_otp_wl_mrr-1 downto 0);  -- Read Voltage Regulator mode control
    CLKOUT    : out std_logic;                                  -- Buffered clock from VPP generator
    PPCLKOUT  : out std_logic;                                  -- internal oscillator output
    -- OTP Array Control
    OE        : in  std_logic;                                  -- 
    SEL       : in  std_logic;                                  -- 
    WE        : in  std_logic;                                  -- 
    CK        : in  std_logic;                                  -- Address/Data/Command Strobe
    MR        : in  std_logic_vector(c_otp_wl_mr-1 downto 0);   -- Read and Test mode control pins
    ADDR      : in  std_logic_vector(c_otp_wl_adr-1 downto 0);  -- address
    DW        : in  std_logic_vector(c_otp_wl_word-1 downto 0); -- data write
    DR        : out std_logic_vector(c_otp_wl_word-1 downto 0); -- data read
    -- Analog signals
    EHV       : in  std_logic;   -- OTP analog input voltage 5V when VDD is stable
    VBG       : out std_logic;   -- OTP analog output voltage for testbus
    VPPPAD    : out std_logic;   -- OTP analog output voltage for high voltage testbus
    VREF      : out std_logic;   -- OTP analog output voltage for testbus
    VRR       : out std_logic    -- OTP analog output voltage for testbus
  );
  end component;
-------------------------------------------------------------------------------
  
  component otp_fpga
    port (
        -- Charge-Pump Control
    VPPEN     : in  std_logic;                                  -- Enable the VPP limiter and VPP charge pump
    VRREN     : in  std_logic;                                  -- Enable the VRR generator, bandgap, bandgap bias, and buffer
    MPP       : in  std_logic_vector(c_otp_wl_mpp-1 downto 0);  -- Charge-Pump mode control
    MRR       : in  std_logic_vector(c_otp_wl_mrr-1 downto 0);  -- Read Voltage Regulator mode control
    CLKOUT    : out std_logic;                                  -- Buffered clock from VPP generator
    PPCLKOUT  : out std_logic;                                  -- internal oscillator output
    -- OTP Array Control
    OE        : in  std_logic;                                  -- 
    SEL       : in  std_logic;                                  -- 
    WE        : in  std_logic;                                  -- 
    CK        : in  std_logic;                                  -- Address/Data/Command Strobe
    MR        : in  std_logic_vector(c_otp_wl_mr-1 downto 0);   -- Read and Test mode control pins
    ADDR      : in  std_logic_vector(c_otp_wl_adr-1 downto 0);  -- address
    DW        : in  std_logic_vector(c_otp_wl_word-1 downto 0); -- data write
    DR        : out std_logic_vector(c_otp_wl_word-1 downto 0); -- data read
    -- Analog signals
--    VCC       : in  std_logic;   -- IPS analog input voltage 5V
    EHV       : in  std_logic;   -- OTP analog input voltage 5V when VDD is stable
    VBG       : out std_logic;   -- OTP analog output voltage for testbus
    VPPPAD    : out std_logic;   -- OTP analog output voltage for high voltage testbus
    VREF      : out std_logic;   -- OTP analog output voltage for testbus
    VRR       : out std_logic    -- OTP analog output voltage for testbus
    );
  end component;
  
  -------------------------------------------------------------------------------
  -- signals
  -------------------------------------------------------------------------------
  
  -- ATPG bypass signals
  signal bypass_collection	: std_logic_vector(62 downto 0);
  signal bypass_value		: std_logic_vector(11 downto 0);
  
  -- OTP input/output
  signal otp_ck       : std_logic;
  signal en_otp_cp    : std_logic;
  signal en_otp_vpp   : std_logic;
  signal otp_oe       : std_logic;
  signal otp_we       : std_logic;
  signal otp_sel      : std_logic;
  
  signal otp_addr     : std_logic_vector(c_otp_wl_adr-1  downto 0);
  signal otp_din      : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal otp_dout     : std_logic_vector(c_otp_wl_word-1 downto 0);
  signal otp_clk      : std_logic;
  signal otp_ppclk    : std_logic;
  
  signal otp_mpp      : std_logic_vector(c_otp_wl_mpp-1 downto 0);
  signal otp_mrr      : std_logic_vector(c_otp_wl_mrr-1 downto 0);
  signal otp_mr       : std_logic_vector(c_otp_wl_mr-1  downto 0);
  
  -- Bypas Flip-Flops
  signal otp_bypass   : std_logic_vector(c_otp_wl_word-1 downto 0);
  
begin -- RTL
  
  -------------------------------------------------------------------------------
  -- ATPG input XOR-chain for complete bypass
  -------------------------------------------------------------------------------
  bypass_collection( 0) <= i_ctrl_cp.vppen;
  bypass_collection( 1) <= i_ctrl_cp.vrren;
  bypass_collection( 9 downto 2) <= i_ctrl_cp.mpp;
  bypass_collection(25 downto 10) <= i_ctrl_cp.mrr;
  bypass_collection(26) <= i_ctrl_otp.ck;
  bypass_collection(27) <= i_ctrl_otp.oe;
  bypass_collection(28) <= i_ctrl_otp.we;
  bypass_collection(29) <= i_ctrl_otp.sel;
  bypass_collection(30) <= i_ctrl_otp.ehv;
  bypass_collection(38 downto 31) <= i_ctrl_otp.mr;
  bypass_collection(50 downto 39) <= i_ctrl_otp.addr;
  bypass_collection(62 downto 51) <= i_data_otp.data;
  
  bypass_value <= bypass_collection(11 downto 0) xor bypass_collection(23 downto 12) xor bypass_collection(35 downto 24) xor bypass_collection(47 downto 36) xor bypass_collection(59 downto 48) xor (bypass_collection(62 downto 60) & "000000000");
  

  -------------------------------------------------------------------------------
  -- ATPG gating for OTP input signals
  -------------------------------------------------------------------------------
  otp_oe       <= '1';
  otp_ck       <= i_ctrl_otp.ck and (not i_atpg_mode);
  otp_we       <= i_ctrl_otp.we and (not i_atpg_mode);
  otp_sel      <= i_ctrl_otp.sel and (not i_atpg_mode);
  
  en_otp_cp    <= i_ctrl_cp.vrren and (not i_atpg_mode);
  en_otp_vpp   <= i_ctrl_cp.vppen and (not i_atpg_mode);
  
  otp_addr     <= i_ctrl_otp.addr;
  otp_din      <= i_data_otp.data;
  otp_mr       <= (others=>'0') when (i_atpg_mode = '1') else i_ctrl_otp.mr; -- synopsys infer_mux_override
  
  otp_mpp      <= (others=>'0') when (i_atpg_mode = '1') else i_ctrl_cp.mpp; -- synopsys infer_mux_override
  otp_mrr      <= (others=>'0') when (i_atpg_mode = '1') else i_ctrl_cp.mrr; -- synopsys infer_mux_override
  
  -------------------------------------------------------------------------------
  -- ATPG bypass for OTP output signals
  -------------------------------------------------------------------------------
  o_data_cp.clkout    <= otp_clk;
  o_data_cp.ppclkout  <= otp_ppclk;
  o_data_otp.data     <= otp_bypass       when (i_atpg_mode = '1') or (i_bypass_mode = '1')
  else                   otp_dout;
  
  -------------------------------------------------------------------------------
  -- Bypass Flip-Flops
  -------------------------------------------------------------------------------
  shift_dr_clk : process(i_nrst, i_clk_sys) begin
    if (i_nrst = '0') then
      otp_bypass  <= (others => '0');
    elsif rising_edge(i_clk_sys) then
      if ((i_atpg_mode = '1') or (i_bypass_mode = '1')) then -- only in bypass mode
        otp_bypass  <= bypass_value;
      end if;
    end if;
  end process shift_dr_clk;
  
  -------------------------------------------------------------------------------
  -- subblocks instantiations
  -------------------------------------------------------------------------------
  gen_tsmc: if target_technology_TSMC generate 
  u_otp4kx12: otp4kx12_cp
  port map (
    -- Charge-Pump Control
    VPPEN     => en_otp_vpp,
    VRREN     => en_otp_cp,
    MPP       => otp_mpp,
    MRR       => otp_mrr,
    CLKOUT    => otp_clk,
    PPCLKOUT  => otp_ppclk,
    -- OTP Array Control
    OE        => otp_oe,
    SEL       => otp_sel,
    WE        => otp_we,
    CK        => otp_ck,
    MR        => otp_mr,
    ADDR      => otp_addr,
    DW        => otp_din,
    DR        => otp_dout,
    -- Analog signals
--   VCC       => a_otp_vcc,
    EHV       => a_otp_ehv,
    VBG       => a_otp_vbg,
    VPPPAD    => a_otp_vpppad,
    VREF      => a_otp_vref,
    VRR       => a_otp_vrr
  );
  end generate gen_tsmc;

  gen_fpga: if target_technology_FPGA generate
    u_otp4kx12 : otp_fpga
      port map (
    -- Charge-Pump Control
    VPPEN     => en_otp_vpp,
    VRREN     => en_otp_cp,
    MPP       => otp_mpp,
    MRR       => otp_mrr,
    CLKOUT    => otp_clk,
    PPCLKOUT  => otp_ppclk,
    -- OTP Array Control
    OE        => otp_oe,
    SEL       => otp_sel,
    WE        => otp_we,
    CK        => otp_ck,
    MR        => otp_mr,
    ADDR      => otp_addr,
    DW        => otp_din,
    DR        => otp_dout,
    -- Analog signals
--    VCC       => a_otp_vcc,
    EHV       => a_otp_ehv,
    VBG       => a_otp_vbg,
    VPPPAD    => a_otp_vpppad,
    VREF      => a_otp_vref,
    VRR       => a_otp_vrr
    );
  end generate gen_fpga;
  -------------------------------------------------------------------------------
end RTL;
