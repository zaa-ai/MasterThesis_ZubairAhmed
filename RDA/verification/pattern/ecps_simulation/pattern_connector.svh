// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Connector File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : pattern_connector.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 16, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class pattern_connector;
  protected timing timings[string];
  protected string current_timing;
  virtual ECPS_pattern_if vif;

  function new(virtual ECPS_pattern_if vif);
    this.vif = vif;
    timings.delete();
    current_timing = "";
  endfunction

  virtual function void add_timing(timing new_timing, string name);
    timings[name] = new_timing;
  endfunction

  virtual task apply_vector(vector_element values[$]);
    timings[current_timing].apply_vector(values);
  endtask

  virtual function void set_comment(string comment);
    vif.comment = string_equivalent'(comment);
  endfunction

  virtual function void set_vector_line(int line_number);
    vif.vector_line = line_number;
  endfunction

  virtual function void set_current_timing(string new_timing);
    if (timings.exists(new_timing)>0)
      current_timing = new_timing;
    else begin
      log_handler _log_handler;
      _log_handler = ecps_configuration::get_log_handler();
      _log_handler.report_error($sformatf("timing %s is not a valid timing", new_timing),,`__FILE__, `__LINE__);
    end
  endfunction
endclass
