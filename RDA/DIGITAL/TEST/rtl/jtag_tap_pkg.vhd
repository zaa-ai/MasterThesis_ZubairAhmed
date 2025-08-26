-------------------------------------------------------------------------------
--! $Author: mslz $
-------------------------------------------------------------------------------
--! (C) COPYRIGHT 2012 ELMOS AG
--! ALL RIGTHS RESERVED
-------------------------------------------------------------------------------
--! $Date: 2013-06-18 17:59:19 +0200 (Tue, 18 Jun 2013) $
-------------------------------------------------------------------------------
--! \brief: package for standard module jtag_tap
-------------------------------------------------------------------------------
--! $Revision: 639 $
--! \section log Revisons
--! Date        Version  Project  Author  Description
--! 2012-03-21  1.0      standard ime     Created
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;

library digital;
use digital.digital_pkg.c_dsr_width;

package jtag_tap_pkg is

  constant c_dsr_width : integer := digital.digital_pkg.c_dsr_width;

  type t_jtag_bus is record
    test_en       : std_logic; -- reset source of all atpg-testable FFs in the testlogic
    -- JTAG signals
    tck           : std_logic;
    tdi           : std_logic;
    tms           : std_logic;
    tdo_latched   : std_logic;
    tdo_unlatched : std_logic;
    -- latched instruction from TAP
    ir            : std_logic_vector(7 downto 0);
    -- Data-Shift-Register control and data
    dsr2tdo       : std_logic;
    dsr           : std_logic_vector(c_dsr_width-1 downto 0);
    -- TAP states unlatched
    test_rst      : std_logic;
    run_idle      : std_logic;
    capture_dr    : std_logic;
    shift_dr      : std_logic;
    update_dr     : std_logic;
    update_ir     : std_logic;
    -- TAP states latched (with falling edge of tck)
    test_rst_fe   : std_logic;
    run_idle_fe   : std_logic;
    capture_dr_fe : std_logic;
    shift_dr_fe   : std_logic;
    update_dr_fe  : std_logic;
    update_ir_fe  : std_logic;
  end record;

end jtag_tap_pkg;
