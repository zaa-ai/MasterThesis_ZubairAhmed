// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Vector Element File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : vector_element.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 16, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class vector_element;
  io_def_t value;
  string variable_name;
  int bit_position;
  logic return_value;

  function new(io_def_t value, string variable_name, int bit_position);
    this.value = value;
    this.variable_name = variable_name;
    this.bit_position = bit_position;
  endfunction
endclass
