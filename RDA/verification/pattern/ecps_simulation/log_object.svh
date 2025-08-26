// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Log Object File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : log_object.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 16, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class log_object;
  protected log_handler _log_handler;

  virtual function void error(string message, string id = "", string filename = "", int line = 0);
    _log_handler = ecps_configuration::get_log_handler();
    _log_handler.report_error(message, id, filename, line);
  endfunction

  virtual function void warning(string message, string id = "", string filename = "", int line = 0);
    _log_handler = ecps_configuration::get_log_handler();
    _log_handler.report_warning(message, id, filename, line);
  endfunction

  virtual function void info(string message, string id = "", string filename = "", int line = 0);
    _log_handler = ecps_configuration::get_log_handler();
    _log_handler.report_info(message, id, filename, line);
  endfunction

  virtual function void fatal(string message, string id = "", string filename = "", int line = 0);
    _log_handler = ecps_configuration::get_log_handler();
    _log_handler.report_fatal(message, id, filename, line);
  endfunction
endclass
