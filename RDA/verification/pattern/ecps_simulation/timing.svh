// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Timing File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : timing.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 16, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

virtual class timing;
  virtual ECPS_pattern_if vif;

  pure virtual task apply_vector(vector_element values[$]);
endclass
