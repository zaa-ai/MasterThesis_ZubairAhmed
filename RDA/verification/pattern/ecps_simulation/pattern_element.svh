// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Element File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : pattern_element.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

interface class pattern_element;
  pure virtual function void parse(pattern_line line);
  pure virtual task execute(pattern_connector connector);
  pure virtual function bit has_value();
endclass
