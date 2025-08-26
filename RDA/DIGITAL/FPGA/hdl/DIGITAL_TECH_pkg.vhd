-------------------------------------------------------------------------------
-- Title      : DIGITAL_TECH_pkg
-- Project    : 
-------------------------------------------------------------------------------
-- File       : DIGITAL_TECH_pkg.vhd
-- Author     : Stephan Richter -DMOS-  <stephan.richter@dmosdesign.com>
-- Company    : 
-- Created    : 2012-02-21
-- Last update: 2017-09-11
-- Platform   : 
-- Standard   : VHDL'87
-------------------------------------------------------------------------------
-- Description: Registeraddresses and more
-------------------------------------------------------------------------------
-- Copyright (c) 2012 
-------------------------------------------------------------------------------
-- Revisions  :
-- Date        Version  Author  Description
-- 2012-02-21  1.0      stri    Created
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

package DIGITAL_TECH_pkg is
  -----------------------------------------------------------------------------
  -- set only one true in this section
  constant target_technology_TCB018GBWP7T: boolean := false;
  constant target_technology_TSMC018_1V8 : boolean := false;  
  constant target_technology_FPGA    : boolean := true;  
  constant target_technology_ELMOS   : boolean := false;
  constant target_technology_ELMOS_S : boolean := false;
  -----------------------------------------------------------------------------
  
  constant target_technology_TSMC    : boolean := target_technology_TCB018GBWP7T or target_technology_TSMC018_1V8;  -- needed for SRAM; ROM; ...  
  constant target_use_fpga_ram       : boolean := false;
  
end DIGITAL_TECH_pkg;
