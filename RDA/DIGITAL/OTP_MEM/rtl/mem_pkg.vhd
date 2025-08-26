-------------------------------------------------------------------------------
-- Title      : package for system memory description
-- Project    : 
-------------------------------------------------------------------------------
-- File       : pkg_address_map.vhd
-- Author     : Markus Scholz / MSLZ /
--              Ilia Leshchev / ILE /
-- Company    : ELMOS Semiconductor AG
-- Created    : XX.XX.XXXX
-- Last update: XX.XX.XXXX
-------------------------------------------------------------------------------
-- Copyright (c) XXXX
-------------------------------------------------------------------------------
-- Revisions  :
-- Date        Version  Author  Description
-- XX.XX.XXXX  1.0      MSLZ    initial
-------------------------------------------------------------------------------

Library ieee;
use ieee.std_logic_1164.all;

package mem_pkg is

  constant c_ip_wl_adr : integer := 12;
  constant c_ip_wl_dat : integer := 12;    -- data word length
  constant c_ip_wl_sel : integer :=  2;    -- data word length

  type t_ip_bus is
    record
      adr : std_logic_vector(c_ip_wl_adr-1 downto 0);
      dat : std_logic_vector(c_ip_wl_dat-1 downto 0);
      we  : std_logic;
      sel : std_logic_vector(c_ip_wl_sel-1 downto 0);
      stb : std_logic;
      ack : std_logic;
      otp_ready : std_logic;
    end record;

end mem_pkg;
