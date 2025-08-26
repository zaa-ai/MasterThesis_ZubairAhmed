
LIBRARY ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;

LIBRARY OTP_MEM;
USE OTP_MEM.otp_wrapper_pkg.all;
use OTP_MEM.mem_pkg.all;

ENTITY otp_fpga IS
PORT(
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
    VRR       : out std_logic    -- OTP analog output voltage for testbus                  --busy / data ready signal
	);
END otp_fpga;

ARCHITECTURE behaviour OF otp_fpga IS

BEGIN
  DR <= (others => '0');
  VBG <= '0';
  VPPPAD <= '0';
  VREF <= '0';
  VRR <= '0';
  CLKOUT <= '0';
  PPCLKOUT <= '0';
END behaviour;
