// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Default Log Handler File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : default_log_handler.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 16, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class default_log_handler implements log_handler;
  int errors;
  int warnings;
  int infos;

  function new();
    errors = 0;
    warnings = 0;
    infos = 0;
  endfunction

  virtual function void report_fatal(string message, string id = "", string filename = "", int line = 0);
    $fatal("FATAL: %s%s file: %s in line %1d", (id=="")?id:{"[",id,"] "}, message, filename, line);
  endfunction

  virtual function void report_error(string message, string id = "", string filename = "", int line = 0);
    $error("ERROR: %s%s file: %s in line %1d", (id=="")?id:{"[",id,"] "}, message, filename, line);
    errors++;
  endfunction

  virtual function void report_warning(string message, string id = "", string filename = "", int line = 0);
    $warning("WARNING: %s%s file: %s in line %1d", (id=="")?id:{"[",id,"] "}, message, filename, line);
    warnings++;
  endfunction

  virtual function void report_info(string message, string id = "", string filename = "", int line = 0);
    $info("INFO: %s%s file: %s in line %1d", (id=="")?id:{"[",id,"] "}, message, filename, line);
    infos++;
  endfunction

  virtual function int get_number_of_errors();
    return errors;
  endfunction

  virtual function int get_number_of_warnings();
    return warnings;
  endfunction

  virtual function int get_number_of_infos();
    return infos;
  endfunction

  static function log_handler create();
    default_log_handler handler;
    handler = new();
    return handler;
  endfunction
endclass
