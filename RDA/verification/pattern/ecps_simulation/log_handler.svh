// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Log Handler File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : log_handler.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 16, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

interface class log_handler;
  pure virtual function void report_fatal(string message, string id = "", string filename = "", int line = 0);
  pure virtual function void report_error(string message, string id = "", string filename = "", int line = 0);
  pure virtual function void report_warning(string message, string id = "", string filename = "", int line = 0);
  pure virtual function void report_info(string message, string id = "", string filename = "", int line = 0);

  pure virtual function int get_number_of_errors();
  pure virtual function int get_number_of_warnings();
  pure virtual function int get_number_of_infos();

endclass
