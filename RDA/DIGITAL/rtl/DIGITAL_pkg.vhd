-------------------------------------------------------------------------------
-- Title      : DIGITAL_pkg
-- Project    : 
-------------------------------------------------------------------------------
-- File       : DIGITAL_pkg.vhd
-- Author     : Stephan Richter -DMOS-  <stephan.richter@dmosdesign.com>
-- Company    : 
-- Created    : 2012-02-21
-- Last update: 2017-07-26
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

library digital;
use digital.digital_tech_pkg.all;

package DIGITAL_pkg is
  
  constant c_dsr_width : integer := 32; -- hint: min elip addr + data length;
  
  -----------------------------------------------------------------------------
  -- define target technology
  -----------------------------------------------------------------------------
  constant target_technology_TCB018GBWP7T   : boolean := DIGITAL.DIGITAL_TECH_pkg.target_technology_TCB018GBWP7T;
  constant target_technology_TSMC018_1V8    : boolean := DIGITAL.DIGITAL_TECH_pkg.target_technology_TSMC018_1V8;
  constant target_technology_TSMC           : boolean := DIGITAL.DIGITAL_TECH_pkg.target_technology_TSMC;
  
  constant target_technology_FPGA           : boolean := DIGITAL.DIGITAL_TECH_pkg.target_technology_FPGA;
  constant target_technology_ELMOS          : boolean := DIGITAL.DIGITAL_TECH_pkg.target_technology_ELMOS;
  constant target_technology_ELMOS_S        : boolean := DIGITAL.DIGITAL_TECH_pkg.target_technology_ELMOS_S;
  constant target_use_fpga_ram              : boolean := DIGITAL.DIGITAL_TECH_pkg.target_use_fpga_ram;
  -----------------------------------------------------------------------------

  
end DIGITAL_pkg;
