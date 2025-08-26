LIBRARY ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;
ENTITY OSC20M IS
    PORT(
       fout20m 	:   OUT 	std_logic;
       fout10m 	:   OUT 	std_logic;
       fout5m 	:   OUT 	std_logic;
       f_trim 	:   IN 		std_logic_vector ( 6 DOWNTO 0 );
       tcf_trim :   IN 		std_logic_vector ( 2 DOWNTO 0 );
       gnd  	:   IN	 	real := 0.0;
       gnd_sub  :   IN	 	real := 0.0;
       offa  	:   IN 		std_logic;   
       abus_en 	:   IN 		std_logic;    
       sfmax 	:   IN 		std_logic; 
       sfmin 	:   IN 		std_logic;  
       ready 	:   OUT 	std_logic;
       abus  	:   OUT	 	real := 0.0;
       abus_i_1v8 : OUT		real := 0.0;
       vdd      :   IN	 	real := 0.0;
	stdc_nbl: 	IN	real:=0.0
    );
END OSC20M;

architecture BEHAVE of OSC20M is

signal      clk20m:     std_logic   :='0';
signal      clk10m:     std_logic   :='0';
signal      clk5m:      std_logic   :='0';
signal      ready_osc:  std_logic   :='1';
signal      pw_trim20m: time        :=50*1ns;
signal      pw_trim10m: time        :=100*1ns;
signal      pw_trim5m:  time        :=200*1ns;
signal      pw_abus:	real        :=0.0;
constant    nom_freq:   real        :=20.0E6;
constant    prd_step:   real        :=0.4E-9;
constant    abus_step:  real        :=0.00315;
constant    set_time:   time        :=20*1us;

begin  fout20m <= clk20m;
       fout10m <= clk10m;
       fout5m  <= clk5m;
----------------------------------------------------------------------------------
-- read trim code, calc freq
  getTrim: process(f_trim, sfmax, sfmin)
  variable   trim_prd:     real  := 50.0E-9;  -- 20 MHz @ trim code '83' 
  variable   prd_highest:  real  := 83.0E-9;  -- 12 MHz @ trim code '0' 
  variable   prd_lowest:   real  := 33.0E-9;  -- 30.5 MHz @ trim code '127' 
  variable   prd_sfmin:    real  := 90.0E-9;  
  variable   prd_sfmax:    real  := 30.0E-9;  
  variable   abus_val:     real  := 0.8;  -- 20 MHz @ trim code '83' 
  variable   abus_lowest:  real  := 0.6;  -- 12 MHz @ trim code '0'
  variable   abus_highest: real  := 1.0;  -- 30.5 MHz @ trim code '127' 
  begin
	if (sfmin = '1') then 
	trim_prd := prd_sfmin;
	abus_val := 0.05;
        else  
	if (sfmax = '1') then 
	trim_prd := prd_sfmax;
	abus_val := 1.75;
	else 
	if ((sfmax = '0') and (sfmin = '0')) then
	    prd_highest := (1.0/nom_freq) + 83.0 * prd_step; 
	    trim_prd 	:= prd_highest - real(conv_integer(f_trim(6 downto 0)))*prd_step;
	    abus_val    := abus_lowest + real(conv_integer(f_trim(6 downto 0)))*abus_step;
	end if; end if; end if; 
	    pw_trim20m  <= (trim_prd)*0.5E9*1ns;
	    pw_trim10m  <= (trim_prd)*1.0E9*1ns;
	    pw_trim5m   <= (trim_prd)*2.0E9*1ns;
	    pw_abus 	<= abus_val;
  end process getTrim;
----------------------------------------------------------------------------------
-- analog test bus function
abus_set: process (vdd, offa, abus_en, pw_abus)
  begin
	if ((offa ='0') and (vdd > 1.2) and (abus_en ='1')) then
		abus <= pw_abus;
		else 
		abus <= 0.0;
	end if;
  end process abus_set;
----------------------------------------------------------------------------------
-- oscillator function
  osc: process(vdd, offa, pw_trim20m, pw_trim10m, pw_trim5m, clk20m, clk10m, clk5m, ready_osc)
  begin
    if ((offa ='0') and (vdd > 1.2)) then
      clk20m <= not clk20m after pw_trim20m;
      clk10m <= not clk10m after pw_trim10m;
      clk5m  <= not clk5m  after pw_trim5m;
      ready  <= ready_osc  after set_time;
    end if;
  end process osc;
----------------------------------------------------------------------------------
-- checks and warning messages (display warning at first violation only)
  check: process(vdd)
  variable vdd_ok         : BOOLEAN := false;
  variable vdd_msgset     : BOOLEAN := false;
  begin
    vdd_ok  := (vdd  > 1.2);
    if not vdd_ok then
      if (not vdd_msgset) and (NOW > 0*1ns) then
        vdd_msgset := true;
        assert false report "v(vdd) < 1.2V" severity warning;
      end if;
    else
      vdd_msgset := false;
    end if; 
  end process check;
----------------------------------------------------------------------------------
end BEHAVE;
