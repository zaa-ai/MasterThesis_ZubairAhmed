// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Line File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : pattern_line.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class pattern_line;
  string line;
  protected int line_number;

  function new(string line, int line_number);
    this.line = line;
    this.line_number = line_number;
    trim();
  endfunction

  function bit is_empty();
    if (line == "")
      return 1'b1;
  endfunction

  function void trim();
    line = line.substr(0, line.len()-2); // remove line feed
  endfunction

  function int get_line_number();
    return line_number;
  endfunction
endclass
