// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Wrapper File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : pattern_wrapper.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 14, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class pattern_wrapper;
  virtual ECPS_pattern_if vif;
  value_set_e current_value_set;

  function new(virtual ECPS_pattern_if _vif);
    this.vif = _vif;
    this.vif.vector_line = 0;
    this.vif.current_task = NONE;
    this.vif.mismatch = 1'b0;
  endfunction

  virtual task run(string pattern);
    pattern_connector connector;
    ecps_pattern_parser parser;

    connector = new(vif);
    add_timings(connector);

    vif.current_task = string_equivalent'(pattern);
    parser = new();
    `define STRING_OF(x) `"x`"
    `ifndef PATTERN_FILE_LOCATION
    `define PATTERN_FILE_LOCATION
    `endif
	parser.parse({`STRING_OF(`PATTERN_FILE_LOCATION), pattern, ".efv"}, connector);
    vif.current_task = NONE;
  endtask

  virtual function void add_timings(pattern_connector connector);
  endfunction
endclass
