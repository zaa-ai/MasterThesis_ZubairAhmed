// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Parser File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : parser.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

interface class parser;
  pure virtual task parse(string file_name, pattern_connector connector);
endclass
