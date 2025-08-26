// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Timeplate File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : ecps_pattern_timeplate.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class ecps_pattern_timeplate implements pattern_element;
  protected string timeplate;
  function new();
    timeplate = "";
  endfunction

  virtual function void parse(pattern_line line);
    if (line.line.match("^t:\\s*(\\S+)(.*)")>0) begin
      timeplate = line.line.backref(0);
      line.line = line.line.backref(1);
    end
  endfunction

  virtual function bit has_value();
    if (timeplate == "") return 1'b0;
    else return 1'b1;
  endfunction

  static function bit add(pattern_line line, ref pattern_element elements[$]);
    ecps_pattern_timeplate new_timeplate;
    new_timeplate = new();
    new_timeplate.parse(line);
    if (new_timeplate.has_value()) begin
      elements.push_back(new_timeplate);
      return 1'b1;
    end
    else
      return 1'b0;
  endfunction

  virtual task execute(pattern_connector connector);
    connector.set_current_timing(timeplate);
  endtask
endclass
