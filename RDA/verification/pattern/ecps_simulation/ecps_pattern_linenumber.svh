// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Line Number File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : ecps_pattern_linenumber.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class ecps_pattern_linenumber implements pattern_element;
  int line_number;

  function new();
    line_number = 0;
  endfunction

  virtual function void parse(pattern_line line);
    line_number = line.get_line_number();
  endfunction

  virtual function bit has_value();
    if (line_number == 0) return 1'b0;
    else return 1'b1;
  endfunction

  static function bit add(pattern_line line, ref pattern_element elements[$]);
    ecps_pattern_linenumber new_line_number;
    new_line_number = new();
    new_line_number.parse(line);
    if (new_line_number.has_value()) begin
      elements.push_back(new_line_number);
      return 1'b1;
    end
    else
      return 1'b0;
  endfunction

  virtual task execute(pattern_connector connector);
    connector.set_vector_line(line_number);
  endtask
endclass
