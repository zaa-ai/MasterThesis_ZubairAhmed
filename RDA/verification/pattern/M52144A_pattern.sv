// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Package/Module File
// ------------------------------------------------------------------------------

`timescale 1ns/1ps

package M52144A_pattern_pkg;
  typedef enum {VS_default} value_set_e;

  import ecps_simulation_pkg::*;
  `include "pattern_wrapper.svh"

  virtual class timing_value_sets extends timing;
    real PAR_jtag4w_per_default = 500;
    real PAR_jtag4w_raise = 0.4;
    real PAR_jtag4w_fall = 0.9;
    real PAR_jtag4w_compare = 0.8;

    pure virtual task apply_vector(vector_element values[$]);

    virtual function void set_value_set(value_set_e value_set);
      case(value_set)
        VS_default: begin
          PAR_jtag4w_per_default = 500;
          PAR_jtag4w_raise = 0.4;
          PAR_jtag4w_fall = 0.9;
          PAR_jtag4w_compare = 0.8;
        end
      endcase
    endfunction
  endclass

  class Timing_Default extends timing_value_sets;
    static function Timing_Default create(virtual ECPS_pattern_if _vif, value_set_e value_set);
      Timing_Default new_timing;
      new_timing = new();
      new_timing.vif = _vif;
      new_timing.set_value_set(value_set);

      return new_timing;
    endfunction

    virtual task apply_vector(vector_element values[$]);
      vif.mismatch = 1'b0;

      fork
        SIGNAL_Timing_Default_BFWB_TCK_MDMA_DPIN(values[0]);
        SIGNAL_Timing_Default_DAB_TMS_MDMA_DPIN(values[1]);
        SIGNAL_Timing_Default_SYNCB_TDI_MDMA_DPIN(values[2]);
        SIGNAL_Timing_Default_INTB_TDO_MDMA_DPIN(values[3]);
      join_none

      #((1000) * 1ns);
    endtask

    task SIGNAL_Timing_Default_BFWB_TCK_MDMA_DPIN(input vector_element io_BFWB_TCK_MDMA_DPIN);
      case (io_BFWB_TCK_MDMA_DPIN.value)
        D0, DZ: #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_BFWB_TCK_MDMA_DPIN.value);
        D1: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'b0;
            #((250) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'b1;
            #((750) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'b0;
          join
        end
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((950) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("BFWB_TCK_MDMA_DPIN", vif.BFWB_TCK_MDMA_DPIN, io_BFWB_TCK_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((950) * 1ns) io_BFWB_TCK_MDMA_DPIN.return_value = vif.BFWB_TCK_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_Timing_Default_DAB_TMS_MDMA_DPIN(input vector_element i_DAB_TMS_MDMA_DPIN);
      case (i_DAB_TMS_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.DAB_TMS_MDMA_DPIN = ecps_simulation_pkg::get_logic(i_DAB_TMS_MDMA_DPIN.value);
      endcase
    endtask

    task SIGNAL_Timing_Default_SYNCB_TDI_MDMA_DPIN(input vector_element io_SYNCB_TDI_MDMA_DPIN);
      case (io_SYNCB_TDI_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.SYNCB_TDI_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_SYNCB_TDI_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((950) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("SYNCB_TDI_MDMA_DPIN", vif.SYNCB_TDI_MDMA_DPIN, io_SYNCB_TDI_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((950) * 1ns) io_SYNCB_TDI_MDMA_DPIN.return_value = vif.SYNCB_TDI_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_Timing_Default_INTB_TDO_MDMA_DPIN(input vector_element i_INTB_TDO_MDMA_DPIN);
      case (i_INTB_TDO_MDMA_DPIN.value)
        EL, EH, EX, EM, EV: begin
          #((950) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("INTB_TDO_MDMA_DPIN", vif.INTB_TDO_MDMA_DPIN, i_INTB_TDO_MDMA_DPIN.value, vif.vector_line);
        end
        CAPTURE: begin
          #((950) * 1ns) i_INTB_TDO_MDMA_DPIN.return_value = vif.INTB_TDO_MDMA_DPIN;
        end
      endcase
    endtask
  endclass

  class clkref_pulse_pat_Timing extends timing_value_sets;
    static function clkref_pulse_pat_Timing create(virtual ECPS_pattern_if _vif, value_set_e value_set);
      clkref_pulse_pat_Timing new_timing;
      new_timing = new();
      new_timing.vif = _vif;
      new_timing.set_value_set(value_set);

      return new_timing;
    endfunction

    virtual task apply_vector(vector_element values[$]);
      vif.mismatch = 1'b0;

      fork
        SIGNAL_clkref_pulse_pat_Timing_BFWB_TCK_MDMA_DPIN(values[0]);
        SIGNAL_clkref_pulse_pat_Timing_DAB_TMS_MDMA_DPIN(values[1]);
        SIGNAL_clkref_pulse_pat_Timing_SYNCB_TDI_MDMA_DPIN(values[2]);
        SIGNAL_clkref_pulse_pat_Timing_INTB_TDO_MDMA_DPIN(values[3]);
      join_none

      #((8) * 1ns);
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_BFWB_TCK_MDMA_DPIN(input vector_element io_BFWB_TCK_MDMA_DPIN);
      case (io_BFWB_TCK_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.BFWB_TCK_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_BFWB_TCK_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("BFWB_TCK_MDMA_DPIN", vif.BFWB_TCK_MDMA_DPIN, io_BFWB_TCK_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) io_BFWB_TCK_MDMA_DPIN.return_value = vif.BFWB_TCK_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_DAB_TMS_MDMA_DPIN(input vector_element i_DAB_TMS_MDMA_DPIN);
      case (i_DAB_TMS_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.DAB_TMS_MDMA_DPIN = ecps_simulation_pkg::get_logic(i_DAB_TMS_MDMA_DPIN.value);
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_SYNCB_TDI_MDMA_DPIN(input vector_element io_SYNCB_TDI_MDMA_DPIN);
      case (io_SYNCB_TDI_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.SYNCB_TDI_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_SYNCB_TDI_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("SYNCB_TDI_MDMA_DPIN", vif.SYNCB_TDI_MDMA_DPIN, io_SYNCB_TDI_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) io_SYNCB_TDI_MDMA_DPIN.return_value = vif.SYNCB_TDI_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_INTB_TDO_MDMA_DPIN(input vector_element i_INTB_TDO_MDMA_DPIN);
      case (i_INTB_TDO_MDMA_DPIN.value)
        EL, EH, EX, EM, EV: begin
          #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("INTB_TDO_MDMA_DPIN", vif.INTB_TDO_MDMA_DPIN, i_INTB_TDO_MDMA_DPIN.value, vif.vector_line);
        end
        CAPTURE: begin
          #((0) * 1ns) i_INTB_TDO_MDMA_DPIN.return_value = vif.INTB_TDO_MDMA_DPIN;
        end
      endcase
    endtask
  endclass

  class clkref_pulse_pat_Timing_h4 extends timing_value_sets;
    static function clkref_pulse_pat_Timing_h4 create(virtual ECPS_pattern_if _vif, value_set_e value_set);
      clkref_pulse_pat_Timing_h4 new_timing;
      new_timing = new();
      new_timing.vif = _vif;
      new_timing.set_value_set(value_set);

      return new_timing;
    endfunction

    virtual task apply_vector(vector_element values[$]);
      vif.mismatch = 1'b0;

      fork
        SIGNAL_clkref_pulse_pat_Timing_h4_BFWB_TCK_MDMA_DPIN(values[0]);
        SIGNAL_clkref_pulse_pat_Timing_h4_DAB_TMS_MDMA_DPIN(values[1]);
        SIGNAL_clkref_pulse_pat_Timing_h4_SYNCB_TDI_MDMA_DPIN(values[2]);
        SIGNAL_clkref_pulse_pat_Timing_h4_INTB_TDO_MDMA_DPIN(values[3]);
      join_none

      #((8) * 1ns);
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_h4_BFWB_TCK_MDMA_DPIN(input vector_element io_BFWB_TCK_MDMA_DPIN);
      case (io_BFWB_TCK_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.BFWB_TCK_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_BFWB_TCK_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("BFWB_TCK_MDMA_DPIN", vif.BFWB_TCK_MDMA_DPIN, io_BFWB_TCK_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) io_BFWB_TCK_MDMA_DPIN.return_value = vif.BFWB_TCK_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_h4_DAB_TMS_MDMA_DPIN(input vector_element i_DAB_TMS_MDMA_DPIN);
      case (i_DAB_TMS_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.DAB_TMS_MDMA_DPIN = ecps_simulation_pkg::get_logic(i_DAB_TMS_MDMA_DPIN.value);
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_h4_SYNCB_TDI_MDMA_DPIN(input vector_element io_SYNCB_TDI_MDMA_DPIN);
      case (io_SYNCB_TDI_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.SYNCB_TDI_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_SYNCB_TDI_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("SYNCB_TDI_MDMA_DPIN", vif.SYNCB_TDI_MDMA_DPIN, io_SYNCB_TDI_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) io_SYNCB_TDI_MDMA_DPIN.return_value = vif.SYNCB_TDI_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_h4_INTB_TDO_MDMA_DPIN(input vector_element i_INTB_TDO_MDMA_DPIN);
      case (i_INTB_TDO_MDMA_DPIN.value)
        EL, EH, EX, EM, EV: begin
          #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("INTB_TDO_MDMA_DPIN", vif.INTB_TDO_MDMA_DPIN, i_INTB_TDO_MDMA_DPIN.value, vif.vector_line);
        end
        CAPTURE: begin
          #((0) * 1ns) i_INTB_TDO_MDMA_DPIN.return_value = vif.INTB_TDO_MDMA_DPIN;
        end
      endcase
    endtask
  endclass

  class clkref_pulse_pat_Timing_l4 extends timing_value_sets;
    static function clkref_pulse_pat_Timing_l4 create(virtual ECPS_pattern_if _vif, value_set_e value_set);
      clkref_pulse_pat_Timing_l4 new_timing;
      new_timing = new();
      new_timing.vif = _vif;
      new_timing.set_value_set(value_set);

      return new_timing;
    endfunction

    virtual task apply_vector(vector_element values[$]);
      vif.mismatch = 1'b0;

      fork
        SIGNAL_clkref_pulse_pat_Timing_l4_BFWB_TCK_MDMA_DPIN(values[0]);
        SIGNAL_clkref_pulse_pat_Timing_l4_DAB_TMS_MDMA_DPIN(values[1]);
        SIGNAL_clkref_pulse_pat_Timing_l4_SYNCB_TDI_MDMA_DPIN(values[2]);
        SIGNAL_clkref_pulse_pat_Timing_l4_INTB_TDO_MDMA_DPIN(values[3]);
      join_none

      #((8) * 1ns);
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_l4_BFWB_TCK_MDMA_DPIN(input vector_element io_BFWB_TCK_MDMA_DPIN);
      case (io_BFWB_TCK_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.BFWB_TCK_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_BFWB_TCK_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("BFWB_TCK_MDMA_DPIN", vif.BFWB_TCK_MDMA_DPIN, io_BFWB_TCK_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) io_BFWB_TCK_MDMA_DPIN.return_value = vif.BFWB_TCK_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_l4_DAB_TMS_MDMA_DPIN(input vector_element i_DAB_TMS_MDMA_DPIN);
      case (i_DAB_TMS_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.DAB_TMS_MDMA_DPIN = ecps_simulation_pkg::get_logic(i_DAB_TMS_MDMA_DPIN.value);
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_l4_SYNCB_TDI_MDMA_DPIN(input vector_element io_SYNCB_TDI_MDMA_DPIN);
      case (io_SYNCB_TDI_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.SYNCB_TDI_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_SYNCB_TDI_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("SYNCB_TDI_MDMA_DPIN", vif.SYNCB_TDI_MDMA_DPIN, io_SYNCB_TDI_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((0) * 1ns) io_SYNCB_TDI_MDMA_DPIN.return_value = vif.SYNCB_TDI_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_clkref_pulse_pat_Timing_l4_INTB_TDO_MDMA_DPIN(input vector_element i_INTB_TDO_MDMA_DPIN);
      case (i_INTB_TDO_MDMA_DPIN.value)
        EL, EH, EX, EM, EV: begin
          #((0) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("INTB_TDO_MDMA_DPIN", vif.INTB_TDO_MDMA_DPIN, i_INTB_TDO_MDMA_DPIN.value, vif.vector_line);
        end
        CAPTURE: begin
          #((0) * 1ns) i_INTB_TDO_MDMA_DPIN.return_value = vif.INTB_TDO_MDMA_DPIN;
        end
      endcase
    endtask
  endclass

  class JTAG_4w_default extends timing_value_sets;
    static function JTAG_4w_default create(virtual ECPS_pattern_if _vif, value_set_e value_set);
      JTAG_4w_default new_timing;
      new_timing = new();
      new_timing.vif = _vif;
      new_timing.set_value_set(value_set);

      return new_timing;
    endfunction

    virtual task apply_vector(vector_element values[$]);
      vif.mismatch = 1'b0;

      fork
        SIGNAL_JTAG_4w_default_BFWB_TCK_MDMA_DPIN(values[0]);
        SIGNAL_JTAG_4w_default_DAB_TMS_MDMA_DPIN(values[1]);
        SIGNAL_JTAG_4w_default_SYNCB_TDI_MDMA_DPIN(values[2]);
        SIGNAL_JTAG_4w_default_INTB_TDO_MDMA_DPIN(values[3]);
      join_none

      #((PAR_jtag4w_per_default) * 1ns);
    endtask

    task SIGNAL_JTAG_4w_default_BFWB_TCK_MDMA_DPIN(input vector_element io_BFWB_TCK_MDMA_DPIN);
      case (io_BFWB_TCK_MDMA_DPIN.value)
        D0, DZ: #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_BFWB_TCK_MDMA_DPIN.value);
        D1: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'b0;
            #((PAR_jtag4w_raise * PAR_jtag4w_per_default) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'b1;
            #((PAR_jtag4w_fall * PAR_jtag4w_per_default) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'b0;
          join
        end
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((PAR_jtag4w_compare * PAR_jtag4w_per_default) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("BFWB_TCK_MDMA_DPIN", vif.BFWB_TCK_MDMA_DPIN, io_BFWB_TCK_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
            #((PAR_jtag4w_compare * PAR_jtag4w_per_default) * 1ns) io_BFWB_TCK_MDMA_DPIN.return_value = vif.BFWB_TCK_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_JTAG_4w_default_DAB_TMS_MDMA_DPIN(input vector_element i_DAB_TMS_MDMA_DPIN);
      case (i_DAB_TMS_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.DAB_TMS_MDMA_DPIN = ecps_simulation_pkg::get_logic(i_DAB_TMS_MDMA_DPIN.value);
      endcase
    endtask

    task SIGNAL_JTAG_4w_default_SYNCB_TDI_MDMA_DPIN(input vector_element io_SYNCB_TDI_MDMA_DPIN);
      case (io_SYNCB_TDI_MDMA_DPIN.value)
        D0, D1, DZ: #0ns vif.SYNCB_TDI_MDMA_DPIN_out = ecps_simulation_pkg::get_logic(io_SYNCB_TDI_MDMA_DPIN.value);
        EL, EH, EX, EM, EV: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((PAR_jtag4w_compare * PAR_jtag4w_per_default) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("SYNCB_TDI_MDMA_DPIN", vif.SYNCB_TDI_MDMA_DPIN, io_SYNCB_TDI_MDMA_DPIN.value, vif.vector_line);
          join
        end
        CAPTURE: begin
          fork
            #((0) * 1ns) vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
            #((PAR_jtag4w_compare * PAR_jtag4w_per_default) * 1ns) io_SYNCB_TDI_MDMA_DPIN.return_value = vif.SYNCB_TDI_MDMA_DPIN;
          join
        end
      endcase
    endtask

    task SIGNAL_JTAG_4w_default_INTB_TDO_MDMA_DPIN(input vector_element i_INTB_TDO_MDMA_DPIN);
      case (i_INTB_TDO_MDMA_DPIN.value)
        EL, EH, EX, EM, EV: begin
          #((PAR_jtag4w_compare * PAR_jtag4w_per_default) * 1ns) vif.mismatch |= ecps_simulation_pkg::check("INTB_TDO_MDMA_DPIN", vif.INTB_TDO_MDMA_DPIN, i_INTB_TDO_MDMA_DPIN.value, vif.vector_line);
        end
        CAPTURE: begin
          #((PAR_jtag4w_compare * PAR_jtag4w_per_default) * 1ns) i_INTB_TDO_MDMA_DPIN.return_value = vif.INTB_TDO_MDMA_DPIN;
        end
      endcase
    endtask
  endclass

  class M52144A_pattern_wrapper extends pattern_wrapper;
    function new(virtual ECPS_pattern_if _vif);
      super.new(_vif);
	  vif.DAB_TMS_MDMA_DPIN  = 1'bz;
      vif.BFWB_TCK_MDMA_DPIN_out = 1'bz;
      vif.SYNCB_TDI_MDMA_DPIN_out = 1'bz;
    endfunction

    virtual function void add_timings(pattern_connector connector);
      connector.add_timing(Timing_Default::create(connector.vif, current_value_set), "Timing_Default");
      connector.add_timing(clkref_pulse_pat_Timing::create(connector.vif, current_value_set), "clkref_pulse_pat_Timing");
      connector.add_timing(clkref_pulse_pat_Timing_h4::create(connector.vif, current_value_set), "clkref_pulse_pat_Timing_h4");
      connector.add_timing(clkref_pulse_pat_Timing_l4::create(connector.vif, current_value_set), "clkref_pulse_pat_Timing_l4");
      connector.add_timing(JTAG_4w_default::create(connector.vif, current_value_set), "JTAG_4w_default");
    endfunction

    virtual function void set_value_set(value_set_e value_set);
      current_value_set = value_set;
    endfunction

    task run_SET_DSI_REC_FALL_0111();
      run("simulation_SET_DSI_REC_FALL_0111");
    endtask

    task run_SET_DSI_TX_DAC_00001();
      run("simulation_SET_DSI_TX_DAC_00001");
    endtask

    task run_SET_DSI_REC_RISE_1111();
      run("simulation_SET_DSI_REC_RISE_1111");
    endtask

    task run_SET_DSI_REC_RISE_1011();
      run("simulation_SET_DSI_REC_RISE_1011");
    endtask

    task run_SET_DSI_REC_FALL_0011();
      run("simulation_SET_DSI_REC_FALL_0011");
    endtask

    task run_VPP_TRIM_TEST();
      run("simulation_VPP_TRIM_TEST");
    endtask

    task run_SET_TM_PADS_OUT_L1();
      run("simulation_SET_TM_PADS_OUT_L1");
    endtask

    task run_VPP_LEVEL_TEST();
      run("simulation_VPP_LEVEL_TEST");
    endtask

    task run_OTP_WRITE_BIST();
      run("simulation_OTP_WRITE_BIST");
    endtask

    task run_OTP_WRITE_PREPARE();
      run("simulation_OTP_WRITE_PREPARE");
    endtask

    task run_OTP_WRITE_SEQ();
      run("simulation_OTP_WRITE_SEQ");
    endtask

    task run_OTP_WRITE_STATUS();
      run("simulation_OTP_WRITE_STATUS");
    endtask

    task run_OTP_WRITE_WAIT();
      run("simulation_OTP_WRITE_WAIT");
    endtask

    task run_SET_ATB_VPP_INT_LOAD();
      run("simulation_SET_ATB_VPP_INT_LOAD");
    endtask

    task run_SET_VRR_0x0F();
      run("simulation_SET_VRR_0x0F");
    endtask

    task run_OTP_PREP_CLEAR_FAST_TEST();
      run("simulation_OTP_PREP_CLEAR_FAST_TEST");
    endtask

    task run_SET_DSI_REC_RISE_1100();
      run("simulation_SET_DSI_REC_RISE_1100");
    endtask

    task run_SET_DSI_TX_DAC_00010();
      run("simulation_SET_DSI_TX_DAC_00010");
    endtask

    task run_SET_DSI_REC_FALL_0100();
      run("simulation_SET_DSI_REC_FALL_0100");
    endtask

    task run_SET_TAP_RESET_TM_SCAN_COMPR();
      run("simulation_SET_TAP_RESET_TM_SCAN_COMPR");
    endtask

    task run_SET_DSI_REC_FALL_0000();
      run("simulation_SET_DSI_REC_FALL_0000");
    endtask

    task run_test_osc_TM_CLK_FILT();
      run("simulation_test_osc_TM_CLK_FILT");
    endtask

    task run_test_osc_TM_CLK_OSC_DIV();
      run("simulation_test_osc_TM_CLK_OSC_DIV");
    endtask

    task run_test_osc_TM_CLK_PLL_DIV();
      run("simulation_test_osc_TM_CLK_PLL_DIV");
    endtask

    task run_test_osc_TM_CLK_SYS_DIV();
      run("simulation_test_osc_TM_CLK_SYS_DIV");
    endtask

    task run_test_osc_TM_CLK_ready_chk_0();
      run("simulation_test_osc_TM_CLK_ready_chk_0");
    endtask

    task run_test_osc_TM_CLK_ready_chk_1();
      run("simulation_test_osc_TM_CLK_ready_chk_1");
    endtask

    task run_test_osc_TM_CLK_reset();
      run("simulation_test_osc_TM_CLK_reset");
    endtask

    task run_test_osc_TM_CLKref_divider();
      run("simulation_test_osc_TM_CLKref_divider");
    endtask

    task run_test_osc_TM_PLL_HOLD();
      run("simulation_test_osc_TM_PLL_HOLD");
    endtask

    task run_test_osc_TM_PLL_HOLD_reset();
      run("simulation_test_osc_TM_PLL_HOLD_reset");
    endtask

    task run_test_osc_TM_PLL_reset();
      run("simulation_test_osc_TM_PLL_reset");
    endtask

    task run_test_osc_TRIM_OSC();
      run("simulation_test_osc_TRIM_OSC");
    endtask

    task run_SET_DSI_REC_RISE_1000();
      run("simulation_SET_DSI_REC_RISE_1000");
    endtask

    task run_Clock_MOSI();
      run("simulation_Clock_MOSI");
    endtask

    task run_clkref_lopulse();
      run("simulation_clkref_lopulse");
    endtask

    task run_OTP_WRITE_int_BIST();
      run("simulation_OTP_WRITE_int_BIST");
    endtask

    task run_SET_DSI_REC_RISE_1101();
      run("simulation_SET_DSI_REC_RISE_1101");
    endtask

    task run_SET_DSI_REC_FALL_0101();
      run("simulation_SET_DSI_REC_FALL_0101");
    endtask

    task run_OTP_BITLINE_CONTI_TEST();
      run("simulation_OTP_BITLINE_CONTI_TEST");
    endtask

    task run_gpio_TM_PADS_HZ();
      run("simulation_gpio_TM_PADS_HZ");
    endtask

    task run_gpio_TM_PADS_IN1();
      run("simulation_gpio_TM_PADS_IN1");
    endtask

    task run_gpio_TM_PADS_IN2();
      run("simulation_gpio_TM_PADS_IN2");
    endtask

    task run_gpio_TM_PADS_OUT_H();
      run("simulation_gpio_TM_PADS_OUT_H");
    endtask

    task run_gpio_TM_PADS_OUT_L();
      run("simulation_gpio_TM_PADS_OUT_L");
    endtask

    task run_gpio_TM_PADS_reset();
      run("simulation_gpio_TM_PADS_reset");
    endtask

    task run_SET_DSI_REC_FALL_0001();
      run("simulation_SET_DSI_REC_FALL_0001");
    endtask

    task run_SET_DSI_REC_RISE_1001();
      run("simulation_SET_DSI_REC_RISE_1001");
    endtask

    task run_OTP_READ_ALL_ARRAY();
      run("simulation_OTP_READ_ALL_ARRAY");
    endtask

    task run_SET_DSI_REC_FALL_0110();
      run("simulation_SET_DSI_REC_FALL_0110");
    endtask

    task run_SET_DSI_TX_DAC_00000();
      run("simulation_SET_DSI_TX_DAC_00000");
    endtask

    task run_SET_DSI_REC_RISE_1110();
      run("simulation_SET_DSI_REC_RISE_1110");
    endtask

    task run_SET_DSI_TX_DAC_11111();
      run("simulation_SET_DSI_TX_DAC_11111");
    endtask

    task run_SET_DSI_REC_RISE_1010();
      run("simulation_SET_DSI_REC_RISE_1010");
    endtask

    task run_SET_DSI_TX_DAC_00100();
      run("simulation_SET_DSI_TX_DAC_00100");
    endtask

    task run_SET_TAP_RESET();
      run("simulation_SET_TAP_RESET");
    endtask

    task run_SET_DSI_REC_FALL_0010();
      run("simulation_SET_DSI_REC_FALL_0010");
    endtask

    task run_SET_TM_PADS_OUT_L0();
      run("simulation_SET_TM_PADS_OUT_L0");
    endtask

    task run_OTP_CELL_CURRENT();
      run("simulation_OTP_CELL_CURRENT");
    endtask

    task run_SET_TAP_RESET_IC_INIT();
      run("simulation_SET_TAP_RESET_IC_INIT");
    endtask

    task run_On_VDD18();
      run("simulation_On_VDD18");
    endtask

    task run_clkref_hipulse();
      run("simulation_clkref_hipulse");
    endtask

    task run_SET_DSI_REC_RISE_0010();
      run("simulation_SET_DSI_REC_RISE_0010");
    endtask

    task run_OTP_PREP_STRESS_TEST();
      run("simulation_OTP_PREP_STRESS_TEST");
    endtask

    task run_SET_DSI_REC_FALL_1010();
      run("simulation_SET_DSI_REC_FALL_1010");
    endtask

    task run_SET_DSI_REC_FALL_1110();
      run("simulation_SET_DSI_REC_FALL_1110");
    endtask

    task run_SET_DSI_TX_DAC_01000();
      run("simulation_SET_DSI_TX_DAC_01000");
    endtask

    task run_SET_DSI_REC_RISE_0110();
      run("simulation_SET_DSI_REC_RISE_0110");
    endtask

    task run_Off_ATB();
      run("simulation_Off_ATB");
    endtask

    task run_Clock_DSI_RX();
      run("simulation_Clock_DSI_RX");
    endtask

    task run_SET_ATB_VRR_INT_LOAD();
      run("simulation_SET_ATB_VRR_INT_LOAD");
    endtask

    task run_SET_ATB_VRR_NO_LOAD();
      run("simulation_SET_ATB_VRR_NO_LOAD");
    endtask

    task run_VREF_LEVEL_TEST();
      run("simulation_VREF_LEVEL_TEST");
    endtask

    task run_test_supply_ATB_IPS_VBG();
      run("simulation_test_supply_ATB_IPS_VBG");
    endtask

    task run_test_supply_ATB_IPS_VPP();
      run("simulation_test_supply_ATB_IPS_VPP");
    endtask

    task run_test_supply_ATB_IPS_VREF();
      run("simulation_test_supply_ATB_IPS_VREF");
    endtask

    task run_test_supply_ATB_IPS_VRR();
      run("simulation_test_supply_ATB_IPS_VRR");
    endtask

    task run_test_supply_ATB_IPS_VRR_FORCE();
      run("simulation_test_supply_ATB_IPS_VRR_FORCE");
    endtask

    task run_test_supply_ATB_OT_COMP();
      run("simulation_test_supply_ATB_OT_COMP");
    endtask

    task run_test_supply_ATB_OT_VTEMP();
      run("simulation_test_supply_ATB_OT_VTEMP");
    endtask

    task run_test_supply_ATB_SUP_I5U();
      run("simulation_test_supply_ATB_SUP_I5U");
    endtask

    task run_test_supply_ATB_SUP_IB10U();
      run("simulation_test_supply_ATB_SUP_IB10U");
    endtask

    task run_test_supply_ATB_SUP_VBG();
      run("simulation_test_supply_ATB_SUP_VBG");
    endtask

    task run_test_supply_TM_IPS_VRR_OVUV();
      run("simulation_test_supply_TM_IPS_VRR_OVUV");
    endtask

    task run_test_supply_TM_IPS_reset();
      run("simulation_test_supply_TM_IPS_reset");
    endtask

    task run_test_supply_TM_ISUP_IDLE();
      run("simulation_test_supply_TM_ISUP_IDLE");
    endtask

    task run_test_supply_TM_ISUP_RX();
      run("simulation_test_supply_TM_ISUP_RX");
    endtask

    task run_test_supply_TM_ISUP_TX();
      run("simulation_test_supply_TM_ISUP_TX");
    endtask

    task run_test_supply_TM_OT_ERR();
      run("simulation_test_supply_TM_OT_ERR");
    endtask

    task run_test_supply_TM_OT_WARN();
      run("simulation_test_supply_TM_OT_WARN");
    endtask

    task run_test_supply_TM_OT_reset();
      run("simulation_test_supply_TM_OT_reset");
    endtask

    task run_test_supply_TM_SUP_CLDOUV();
      run("simulation_test_supply_TM_SUP_CLDOUV");
    endtask

    task run_test_supply_TM_SUP_CLDOUV_reset();
      run("simulation_test_supply_TM_SUP_CLDOUV_reset");
    endtask

    task run_test_supply_TM_SUP_VCCUV();
      run("simulation_test_supply_TM_SUP_VCCUV");
    endtask

    task run_test_supply_TM_SUP_VCCUV_reset();
      run("simulation_test_supply_TM_SUP_VCCUV_reset");
    endtask

    task run_test_supply_TM_VDD_ILOAD_OFF();
      run("simulation_test_supply_TM_VDD_ILOAD_OFF");
    endtask

    task run_test_supply_TM_VDD_ILOAD_ON();
      run("simulation_test_supply_TM_VDD_ILOAD_ON");
    endtask

    task run_test_supply_TM_VDD_ILOAD_RESET();
      run("simulation_test_supply_TM_VDD_ILOAD_RESET");
    endtask

    task run_test_supply_TRIM_IPS();
      run("simulation_test_supply_TRIM_IPS");
    endtask

    task run_test_supply_TRIM_IREF();
      run("simulation_test_supply_TRIM_IREF");
    endtask

    task run_test_supply_TRIM_OT();
      run("simulation_test_supply_TRIM_OT");
    endtask

    task run_SET_LONG_PULSE_RESB();
      run("simulation_SET_LONG_PULSE_RESB");
    endtask

    task run_test_dsi_ATB_DSI_IDAC_0();
      run("simulation_test_dsi_ATB_DSI_IDAC_0");
    endtask

    task run_test_dsi_ATB_DSI_IDAC_1();
      run("simulation_test_dsi_ATB_DSI_IDAC_1");
    endtask

    task run_test_dsi_ATB_DSI_INN();
      run("simulation_test_dsi_ATB_DSI_INN");
    endtask

    task run_test_dsi_ATB_DSI_INP();
      run("simulation_test_dsi_ATB_DSI_INP");
    endtask

    task run_test_dsi_ATB_DSI_VBN5V_DIV();
      run("simulation_test_dsi_ATB_DSI_VBN5V_DIV");
    endtask

    task run_test_dsi_ATB_DSI_VNC0();
      run("simulation_test_dsi_ATB_DSI_VNC0");
    endtask

    task run_test_dsi_ATB_DSI_VNC2();
      run("simulation_test_dsi_ATB_DSI_VNC2");
    endtask

    task run_test_dsi_ATB_DSI_VNG0();
      run("simulation_test_dsi_ATB_DSI_VNG0");
    endtask

    task run_test_dsi_CALIB_DSI_IDAC();
      run("simulation_test_dsi_CALIB_DSI_IDAC");
    endtask

    task run_test_dsi_TM_DSI_HZMODE_sub();
      run("simulation_test_dsi_TM_DSI_HZMODE_sub");
    endtask

    task run_test_dsi_TM_DSI_OFF_sub();
      run("simulation_test_dsi_TM_DSI_OFF_sub");
    endtask

    task run_test_dsi_TM_DSI_OVUV();
      run("simulation_test_dsi_TM_DSI_OVUV");
    endtask

    task run_test_dsi_TM_DSI_RX1();
      run("simulation_test_dsi_TM_DSI_RX1");
    endtask

    task run_test_dsi_TM_DSI_RX2();
      run("simulation_test_dsi_TM_DSI_RX2");
    endtask

    task run_test_dsi_TM_DSI_RXMODE_sub();
      run("simulation_test_dsi_TM_DSI_RXMODE_sub");
    endtask

    task run_test_dsi_TM_DSI_TXMODE_sub();
      run("simulation_test_dsi_TM_DSI_TXMODE_sub");
    endtask

    task run_test_dsi_TM_DSI_TX_PIN();
      run("simulation_test_dsi_TM_DSI_TX_PIN");
    endtask

    task run_test_dsi_TM_DSI_reset();
      run("simulation_test_dsi_TM_DSI_reset");
    endtask

    task run_test_dsi_TRIM_DSI_IDAC();
      run("simulation_test_dsi_TRIM_DSI_IDAC");
    endtask

    task run_test_dsi_TRIM_DSI_REC_FALL();
      run("simulation_test_dsi_TRIM_DSI_REC_FALL");
    endtask

    task run_test_dsi_TRIM_DSI_REC_RISE();
      run("simulation_test_dsi_TRIM_DSI_REC_RISE");
    endtask

    task run_test_dsi_TRIM_DSI_TX_DAC();
      run("simulation_test_dsi_TRIM_DSI_TX_DAC");
    endtask

    task run_SET_TM_PADS_OUT_H0();
      run("simulation_SET_TM_PADS_OUT_H0");
    endtask

    task run_OTP_WORDLINE_CONTI_TEST_wordline_conti_test();
      run("simulation_OTP_WORDLINE_CONTI_TEST_wordline_conti_test");
    endtask

    task run_SET_DSI_REC_FALL_1001();
      run("simulation_SET_DSI_REC_FALL_1001");
    endtask

    task run_SET_DSI_REC_RISE_0001();
      run("simulation_SET_DSI_REC_RISE_0001");
    endtask

    task run_SET_DSI_TX_DAC_10000();
      run("simulation_SET_DSI_TX_DAC_10000");
    endtask

    task run_OTP_SENS_AMP_TEST_MODE_N_BIST();
      run("simulation_OTP_SENS_AMP_TEST_MODE_N_BIST");
    endtask

    task run_SET_DSI_REC_RISE_0101();
      run("simulation_SET_DSI_REC_RISE_0101");
    endtask

    task run_SET_DSI_REC_FALL_1101();
      run("simulation_SET_DSI_REC_FALL_1101");
    endtask

    task run_Off_VDD18();
      run("simulation_Off_VDD18");
    endtask

    task run_SET_VRR_0x04();
      run("simulation_SET_VRR_0x04");
    endtask

    task run_SET_SHORT_PULSE_RESB();
      run("simulation_SET_SHORT_PULSE_RESB");
    endtask

    task run_SET_VRR_0x08();
      run("simulation_SET_VRR_0x08");
    endtask

    task run_SET_TM_PADS_OUT_H1();
      run("simulation_SET_TM_PADS_OUT_H1");
    endtask

    task run_SET_DSI_REC_FALL_1000();
      run("simulation_SET_DSI_REC_FALL_1000");
    endtask

    task run_SET_DSI_REC_RISE_0000();
      run("simulation_SET_DSI_REC_RISE_0000");
    endtask

    task run_SET_DSI_REC_RISE_0100();
      run("simulation_SET_DSI_REC_RISE_0100");
    endtask

    task run_SET_DSI_REC_FALL_1100();
      run("simulation_SET_DSI_REC_FALL_1100");
    endtask

    task run_OTP_ARRAY_CHECK_CLEAN();
      run("simulation_OTP_ARRAY_CHECK_CLEAN");
    endtask

    task run_OTP_PREP_CLEAR_TEST();
      run("simulation_OTP_PREP_CLEAR_TEST");
    endtask

    task run_SET_DSI_REC_RISE_0011();
      run("simulation_SET_DSI_REC_RISE_0011");
    endtask

    task run_SET_DSI_REC_FALL_1011();
      run("simulation_SET_DSI_REC_FALL_1011");
    endtask

    task run_SET_ATB_VPP_NO_LOAD();
      run("simulation_SET_ATB_VPP_NO_LOAD");
    endtask

    task run_SET_DSI_REC_FALL_1111();
      run("simulation_SET_DSI_REC_FALL_1111");
    endtask

    task run_SET_DSI_REC_RISE_0111();
      run("simulation_SET_DSI_REC_RISE_0111");
    endtask

    task run_test_top_ATB_reset();
      run("simulation_test_top_ATB_reset");
    endtask

    task run_test_top_TM_IC_INIT();
      run("simulation_test_top_TM_IC_INIT");
    endtask

    task run_test_top_TM_IDDQ();
      run("simulation_test_top_TM_IDDQ");
    endtask

    task run_test_top_TM_RAM_BIST_result();
      run("simulation_test_top_TM_RAM_BIST_result");
    endtask

    task run_test_top_TM_RAM_BIST_start();
      run("simulation_test_top_TM_RAM_BIST_start");
    endtask

    task run_test_top_TM_SCAN();
      run("simulation_test_top_TM_SCAN");
    endtask

    task run_test_top_TM_SCAN_COMPR();
      run("simulation_test_top_TM_SCAN_COMPR");
    endtask

    task run_OTP_MISSION_LEAKY();
      run("simulation_OTP_MISSION_LEAKY");
    endtask

    task run_OTP_MISSION_WEAK();
      run("simulation_OTP_MISSION_WEAK");
    endtask

    task run_Clock_CLKREF();
      run("simulation_Clock_CLKREF");
    endtask

  endclass
endpackage

interface ECPS_pattern_if;
  import ecps_simulation_pkg::*;
  import M52144A_pattern_pkg::*;

  logic BFWB_TCK_MDMA_DPIN_out;
  logic BFWB_TCK_MDMA_DPIN;
  logic DAB_TMS_MDMA_DPIN;
  logic SYNCB_TDI_MDMA_DPIN_out;
  logic SYNCB_TDI_MDMA_DPIN;
  logic INTB_TDO_MDMA_DPIN;

  int vector_line;
  string_equivalent comment;
  string_equivalent current_task;
  bit mismatch;
endinterface

module M52144A_pattern(
    inout wire BFWB_TCK_MDMA_DPIN,
    output logic DAB_TMS_MDMA_DPIN,
    inout wire SYNCB_TDI_MDMA_DPIN,
    input logic INTB_TDO_MDMA_DPIN
    );

  import ecps_simulation_pkg::*;
  import M52144A_pattern_pkg::*;

  ECPS_pattern_if connector();
  M52144A_pattern_wrapper wrapper;

  nmos(BFWB_TCK_MDMA_DPIN, connector.BFWB_TCK_MDMA_DPIN_out, 1'b1);
  nmos(SYNCB_TDI_MDMA_DPIN, connector.SYNCB_TDI_MDMA_DPIN_out, 1'b1);

  assign connector.BFWB_TCK_MDMA_DPIN = BFWB_TCK_MDMA_DPIN;
  assign DAB_TMS_MDMA_DPIN = connector.DAB_TMS_MDMA_DPIN;
  assign connector.SYNCB_TDI_MDMA_DPIN = SYNCB_TDI_MDMA_DPIN;
  assign connector.INTB_TDO_MDMA_DPIN = INTB_TDO_MDMA_DPIN;

  task run(input string pattern);
    wrapper.run(pattern);
  endtask

  task run_SET_DSI_REC_FALL_0111();
    wrapper.run_SET_DSI_REC_FALL_0111();
  endtask

  task run_SET_DSI_TX_DAC_00001();
    wrapper.run_SET_DSI_TX_DAC_00001();
  endtask

  task run_SET_DSI_REC_RISE_1111();
    wrapper.run_SET_DSI_REC_RISE_1111();
  endtask

  task run_SET_DSI_REC_RISE_1011();
    wrapper.run_SET_DSI_REC_RISE_1011();
  endtask

  task run_SET_DSI_REC_FALL_0011();
    wrapper.run_SET_DSI_REC_FALL_0011();
  endtask

  task run_VPP_TRIM_TEST();
    wrapper.run_VPP_TRIM_TEST();
  endtask

  task run_SET_TM_PADS_OUT_L1();
    wrapper.run_SET_TM_PADS_OUT_L1();
  endtask

  task run_VPP_LEVEL_TEST();
    wrapper.run_VPP_LEVEL_TEST();
  endtask

  task run_OTP_WRITE_BIST();
    wrapper.run_OTP_WRITE_BIST();
  endtask

  task run_OTP_WRITE_PREPARE();
    wrapper.run_OTP_WRITE_PREPARE();
  endtask

  task run_OTP_WRITE_SEQ();
    wrapper.run_OTP_WRITE_SEQ();
  endtask

  task run_OTP_WRITE_STATUS();
    wrapper.run_OTP_WRITE_STATUS();
  endtask

  task run_OTP_WRITE_WAIT();
    wrapper.run_OTP_WRITE_WAIT();
  endtask

  task run_SET_ATB_VPP_INT_LOAD();
    wrapper.run_SET_ATB_VPP_INT_LOAD();
  endtask

  task run_SET_VRR_0x0F();
    wrapper.run_SET_VRR_0x0F();
  endtask

  task run_OTP_PREP_CLEAR_FAST_TEST();
    wrapper.run_OTP_PREP_CLEAR_FAST_TEST();
  endtask

  task run_SET_DSI_REC_RISE_1100();
    wrapper.run_SET_DSI_REC_RISE_1100();
  endtask

  task run_SET_DSI_TX_DAC_00010();
    wrapper.run_SET_DSI_TX_DAC_00010();
  endtask

  task run_SET_DSI_REC_FALL_0100();
    wrapper.run_SET_DSI_REC_FALL_0100();
  endtask

  task run_SET_TAP_RESET_TM_SCAN_COMPR();
    wrapper.run_SET_TAP_RESET_TM_SCAN_COMPR();
  endtask

  task run_SET_DSI_REC_FALL_0000();
    wrapper.run_SET_DSI_REC_FALL_0000();
  endtask

  task run_test_osc_TM_CLK_FILT();
    wrapper.run_test_osc_TM_CLK_FILT();
  endtask

  task run_test_osc_TM_CLK_OSC_DIV();
    wrapper.run_test_osc_TM_CLK_OSC_DIV();
  endtask

  task run_test_osc_TM_CLK_PLL_DIV();
    wrapper.run_test_osc_TM_CLK_PLL_DIV();
  endtask

  task run_test_osc_TM_CLK_SYS_DIV();
    wrapper.run_test_osc_TM_CLK_SYS_DIV();
  endtask

  task run_test_osc_TM_CLK_ready_chk_0();
    wrapper.run_test_osc_TM_CLK_ready_chk_0();
  endtask

  task run_test_osc_TM_CLK_ready_chk_1();
    wrapper.run_test_osc_TM_CLK_ready_chk_1();
  endtask

  task run_test_osc_TM_CLK_reset();
    wrapper.run_test_osc_TM_CLK_reset();
  endtask

  task run_test_osc_TM_CLKref_divider();
    wrapper.run_test_osc_TM_CLKref_divider();
  endtask

  task run_test_osc_TM_PLL_HOLD();
    wrapper.run_test_osc_TM_PLL_HOLD();
  endtask

  task run_test_osc_TM_PLL_HOLD_reset();
    wrapper.run_test_osc_TM_PLL_HOLD_reset();
  endtask

  task run_test_osc_TM_PLL_reset();
    wrapper.run_test_osc_TM_PLL_reset();
  endtask

  task run_test_osc_TRIM_OSC();
    wrapper.run_test_osc_TRIM_OSC();
  endtask

  task run_SET_DSI_REC_RISE_1000();
    wrapper.run_SET_DSI_REC_RISE_1000();
  endtask

  task run_Clock_MOSI();
    wrapper.run_Clock_MOSI();
  endtask

  task run_clkref_lopulse();
    wrapper.run_clkref_lopulse();
  endtask

  task run_OTP_WRITE_int_BIST();
    wrapper.run_OTP_WRITE_int_BIST();
  endtask

  task run_SET_DSI_REC_RISE_1101();
    wrapper.run_SET_DSI_REC_RISE_1101();
  endtask

  task run_SET_DSI_REC_FALL_0101();
    wrapper.run_SET_DSI_REC_FALL_0101();
  endtask

  task run_OTP_BITLINE_CONTI_TEST();
    wrapper.run_OTP_BITLINE_CONTI_TEST();
  endtask

  task run_gpio_TM_PADS_HZ();
    wrapper.run_gpio_TM_PADS_HZ();
  endtask

  task run_gpio_TM_PADS_IN1();
    wrapper.run_gpio_TM_PADS_IN1();
  endtask

  task run_gpio_TM_PADS_IN2();
    wrapper.run_gpio_TM_PADS_IN2();
  endtask

  task run_gpio_TM_PADS_OUT_H();
    wrapper.run_gpio_TM_PADS_OUT_H();
  endtask

  task run_gpio_TM_PADS_OUT_L();
    wrapper.run_gpio_TM_PADS_OUT_L();
  endtask

  task run_gpio_TM_PADS_reset();
    wrapper.run_gpio_TM_PADS_reset();
  endtask

  task run_SET_DSI_REC_FALL_0001();
    wrapper.run_SET_DSI_REC_FALL_0001();
  endtask

  task run_SET_DSI_REC_RISE_1001();
    wrapper.run_SET_DSI_REC_RISE_1001();
  endtask

  task run_OTP_READ_ALL_ARRAY();
    wrapper.run_OTP_READ_ALL_ARRAY();
  endtask

  task run_SET_DSI_REC_FALL_0110();
    wrapper.run_SET_DSI_REC_FALL_0110();
  endtask

  task run_SET_DSI_TX_DAC_00000();
    wrapper.run_SET_DSI_TX_DAC_00000();
  endtask

  task run_SET_DSI_REC_RISE_1110();
    wrapper.run_SET_DSI_REC_RISE_1110();
  endtask

  task run_SET_DSI_TX_DAC_11111();
    wrapper.run_SET_DSI_TX_DAC_11111();
  endtask

  task run_SET_DSI_REC_RISE_1010();
    wrapper.run_SET_DSI_REC_RISE_1010();
  endtask

  task run_SET_DSI_TX_DAC_00100();
    wrapper.run_SET_DSI_TX_DAC_00100();
  endtask

  task run_SET_TAP_RESET();
    wrapper.run_SET_TAP_RESET();
  endtask

  task run_SET_DSI_REC_FALL_0010();
    wrapper.run_SET_DSI_REC_FALL_0010();
  endtask

  task run_SET_TM_PADS_OUT_L0();
    wrapper.run_SET_TM_PADS_OUT_L0();
  endtask

  task run_OTP_CELL_CURRENT();
    wrapper.run_OTP_CELL_CURRENT();
  endtask

  task run_SET_TAP_RESET_IC_INIT();
    wrapper.run_SET_TAP_RESET_IC_INIT();
  endtask

  task run_On_VDD18();
    wrapper.run_On_VDD18();
  endtask

  task run_clkref_hipulse();
    wrapper.run_clkref_hipulse();
  endtask

  task run_SET_DSI_REC_RISE_0010();
    wrapper.run_SET_DSI_REC_RISE_0010();
  endtask

  task run_OTP_PREP_STRESS_TEST();
    wrapper.run_OTP_PREP_STRESS_TEST();
  endtask

  task run_SET_DSI_REC_FALL_1010();
    wrapper.run_SET_DSI_REC_FALL_1010();
  endtask

  task run_SET_DSI_REC_FALL_1110();
    wrapper.run_SET_DSI_REC_FALL_1110();
  endtask

  task run_SET_DSI_TX_DAC_01000();
    wrapper.run_SET_DSI_TX_DAC_01000();
  endtask

  task run_SET_DSI_REC_RISE_0110();
    wrapper.run_SET_DSI_REC_RISE_0110();
  endtask

  task run_Off_ATB();
    wrapper.run_Off_ATB();
  endtask

  task run_Clock_DSI_RX();
    wrapper.run_Clock_DSI_RX();
  endtask

  task run_SET_ATB_VRR_INT_LOAD();
    wrapper.run_SET_ATB_VRR_INT_LOAD();
  endtask

  task run_SET_ATB_VRR_NO_LOAD();
    wrapper.run_SET_ATB_VRR_NO_LOAD();
  endtask

  task run_VREF_LEVEL_TEST();
    wrapper.run_VREF_LEVEL_TEST();
  endtask

  task run_test_supply_ATB_IPS_VBG();
    wrapper.run_test_supply_ATB_IPS_VBG();
  endtask

  task run_test_supply_ATB_IPS_VPP();
    wrapper.run_test_supply_ATB_IPS_VPP();
  endtask

  task run_test_supply_ATB_IPS_VREF();
    wrapper.run_test_supply_ATB_IPS_VREF();
  endtask

  task run_test_supply_ATB_IPS_VRR();
    wrapper.run_test_supply_ATB_IPS_VRR();
  endtask

  task run_test_supply_ATB_IPS_VRR_FORCE();
    wrapper.run_test_supply_ATB_IPS_VRR_FORCE();
  endtask

  task run_test_supply_ATB_OT_COMP();
    wrapper.run_test_supply_ATB_OT_COMP();
  endtask

  task run_test_supply_ATB_OT_VTEMP();
    wrapper.run_test_supply_ATB_OT_VTEMP();
  endtask

  task run_test_supply_ATB_SUP_I5U();
    wrapper.run_test_supply_ATB_SUP_I5U();
  endtask

  task run_test_supply_ATB_SUP_IB10U();
    wrapper.run_test_supply_ATB_SUP_IB10U();
  endtask

  task run_test_supply_ATB_SUP_VBG();
    wrapper.run_test_supply_ATB_SUP_VBG();
  endtask

  task run_test_supply_TM_IPS_VRR_OVUV();
    wrapper.run_test_supply_TM_IPS_VRR_OVUV();
  endtask

  task run_test_supply_TM_IPS_reset();
    wrapper.run_test_supply_TM_IPS_reset();
  endtask

  task run_test_supply_TM_ISUP_IDLE();
    wrapper.run_test_supply_TM_ISUP_IDLE();
  endtask

  task run_test_supply_TM_ISUP_RX();
    wrapper.run_test_supply_TM_ISUP_RX();
  endtask

  task run_test_supply_TM_ISUP_TX();
    wrapper.run_test_supply_TM_ISUP_TX();
  endtask

  task run_test_supply_TM_OT_ERR();
    wrapper.run_test_supply_TM_OT_ERR();
  endtask

  task run_test_supply_TM_OT_WARN();
    wrapper.run_test_supply_TM_OT_WARN();
  endtask

  task run_test_supply_TM_OT_reset();
    wrapper.run_test_supply_TM_OT_reset();
  endtask

  task run_test_supply_TM_SUP_CLDOUV();
    wrapper.run_test_supply_TM_SUP_CLDOUV();
  endtask

  task run_test_supply_TM_SUP_CLDOUV_reset();
    wrapper.run_test_supply_TM_SUP_CLDOUV_reset();
  endtask

  task run_test_supply_TM_SUP_VCCUV();
    wrapper.run_test_supply_TM_SUP_VCCUV();
  endtask

  task run_test_supply_TM_SUP_VCCUV_reset();
    wrapper.run_test_supply_TM_SUP_VCCUV_reset();
  endtask

  task run_test_supply_TM_VDD_ILOAD_OFF();
    wrapper.run_test_supply_TM_VDD_ILOAD_OFF();
  endtask

  task run_test_supply_TM_VDD_ILOAD_ON();
    wrapper.run_test_supply_TM_VDD_ILOAD_ON();
  endtask

  task run_test_supply_TM_VDD_ILOAD_RESET();
    wrapper.run_test_supply_TM_VDD_ILOAD_RESET();
  endtask

  task run_test_supply_TRIM_IPS();
    wrapper.run_test_supply_TRIM_IPS();
  endtask

  task run_test_supply_TRIM_IREF();
    wrapper.run_test_supply_TRIM_IREF();
  endtask

  task run_test_supply_TRIM_OT();
    wrapper.run_test_supply_TRIM_OT();
  endtask

  task run_SET_LONG_PULSE_RESB();
    wrapper.run_SET_LONG_PULSE_RESB();
  endtask

  task run_test_dsi_ATB_DSI_IDAC_0();
    wrapper.run_test_dsi_ATB_DSI_IDAC_0();
  endtask

  task run_test_dsi_ATB_DSI_IDAC_1();
    wrapper.run_test_dsi_ATB_DSI_IDAC_1();
  endtask

  task run_test_dsi_ATB_DSI_INN();
    wrapper.run_test_dsi_ATB_DSI_INN();
  endtask

  task run_test_dsi_ATB_DSI_INP();
    wrapper.run_test_dsi_ATB_DSI_INP();
  endtask

  task run_test_dsi_ATB_DSI_VBN5V_DIV();
    wrapper.run_test_dsi_ATB_DSI_VBN5V_DIV();
  endtask

  task run_test_dsi_ATB_DSI_VNC0();
    wrapper.run_test_dsi_ATB_DSI_VNC0();
  endtask

  task run_test_dsi_ATB_DSI_VNC2();
    wrapper.run_test_dsi_ATB_DSI_VNC2();
  endtask

  task run_test_dsi_ATB_DSI_VNG0();
    wrapper.run_test_dsi_ATB_DSI_VNG0();
  endtask

  task run_test_dsi_CALIB_DSI_IDAC();
    wrapper.run_test_dsi_CALIB_DSI_IDAC();
  endtask

  task run_test_dsi_TM_DSI_HZMODE_sub();
    wrapper.run_test_dsi_TM_DSI_HZMODE_sub();
  endtask

  task run_test_dsi_TM_DSI_OFF_sub();
    wrapper.run_test_dsi_TM_DSI_OFF_sub();
  endtask

  task run_test_dsi_TM_DSI_OVUV();
    wrapper.run_test_dsi_TM_DSI_OVUV();
  endtask

  task run_test_dsi_TM_DSI_RX1();
    wrapper.run_test_dsi_TM_DSI_RX1();
  endtask

  task run_test_dsi_TM_DSI_RX2();
    wrapper.run_test_dsi_TM_DSI_RX2();
  endtask

  task run_test_dsi_TM_DSI_RXMODE_sub();
    wrapper.run_test_dsi_TM_DSI_RXMODE_sub();
  endtask

  task run_test_dsi_TM_DSI_TXMODE_sub();
    wrapper.run_test_dsi_TM_DSI_TXMODE_sub();
  endtask

  task run_test_dsi_TM_DSI_TX_PIN();
    wrapper.run_test_dsi_TM_DSI_TX_PIN();
  endtask

  task run_test_dsi_TM_DSI_reset();
    wrapper.run_test_dsi_TM_DSI_reset();
  endtask

  task run_test_dsi_TRIM_DSI_IDAC();
    wrapper.run_test_dsi_TRIM_DSI_IDAC();
  endtask

  task run_test_dsi_TRIM_DSI_REC_FALL();
    wrapper.run_test_dsi_TRIM_DSI_REC_FALL();
  endtask

  task run_test_dsi_TRIM_DSI_REC_RISE();
    wrapper.run_test_dsi_TRIM_DSI_REC_RISE();
  endtask

  task run_test_dsi_TRIM_DSI_TX_DAC();
    wrapper.run_test_dsi_TRIM_DSI_TX_DAC();
  endtask

  task run_SET_TM_PADS_OUT_H0();
    wrapper.run_SET_TM_PADS_OUT_H0();
  endtask

  task run_OTP_WORDLINE_CONTI_TEST_wordline_conti_test();
    wrapper.run_OTP_WORDLINE_CONTI_TEST_wordline_conti_test();
  endtask

  task run_SET_DSI_REC_FALL_1001();
    wrapper.run_SET_DSI_REC_FALL_1001();
  endtask

  task run_SET_DSI_REC_RISE_0001();
    wrapper.run_SET_DSI_REC_RISE_0001();
  endtask

  task run_SET_DSI_TX_DAC_10000();
    wrapper.run_SET_DSI_TX_DAC_10000();
  endtask

  task run_OTP_SENS_AMP_TEST_MODE_N_BIST();
    wrapper.run_OTP_SENS_AMP_TEST_MODE_N_BIST();
  endtask

  task run_SET_DSI_REC_RISE_0101();
    wrapper.run_SET_DSI_REC_RISE_0101();
  endtask

  task run_SET_DSI_REC_FALL_1101();
    wrapper.run_SET_DSI_REC_FALL_1101();
  endtask

  task run_Off_VDD18();
    wrapper.run_Off_VDD18();
  endtask

  task run_SET_VRR_0x04();
    wrapper.run_SET_VRR_0x04();
  endtask

  task run_SET_SHORT_PULSE_RESB();
    wrapper.run_SET_SHORT_PULSE_RESB();
  endtask

  task run_SET_VRR_0x08();
    wrapper.run_SET_VRR_0x08();
  endtask

  task run_SET_TM_PADS_OUT_H1();
    wrapper.run_SET_TM_PADS_OUT_H1();
  endtask

  task run_SET_DSI_REC_FALL_1000();
    wrapper.run_SET_DSI_REC_FALL_1000();
  endtask

  task run_SET_DSI_REC_RISE_0000();
    wrapper.run_SET_DSI_REC_RISE_0000();
  endtask

  task run_SET_DSI_REC_RISE_0100();
    wrapper.run_SET_DSI_REC_RISE_0100();
  endtask

  task run_SET_DSI_REC_FALL_1100();
    wrapper.run_SET_DSI_REC_FALL_1100();
  endtask

  task run_OTP_ARRAY_CHECK_CLEAN();
    wrapper.run_OTP_ARRAY_CHECK_CLEAN();
  endtask

  task run_OTP_PREP_CLEAR_TEST();
    wrapper.run_OTP_PREP_CLEAR_TEST();
  endtask

  task run_SET_DSI_REC_RISE_0011();
    wrapper.run_SET_DSI_REC_RISE_0011();
  endtask

  task run_SET_DSI_REC_FALL_1011();
    wrapper.run_SET_DSI_REC_FALL_1011();
  endtask

  task run_SET_ATB_VPP_NO_LOAD();
    wrapper.run_SET_ATB_VPP_NO_LOAD();
  endtask

  task run_SET_DSI_REC_FALL_1111();
    wrapper.run_SET_DSI_REC_FALL_1111();
  endtask

  task run_SET_DSI_REC_RISE_0111();
    wrapper.run_SET_DSI_REC_RISE_0111();
  endtask

  task run_test_top_ATB_reset();
    wrapper.run_test_top_ATB_reset();
  endtask

  task run_test_top_TM_IC_INIT();
    wrapper.run_test_top_TM_IC_INIT();
  endtask

  task run_test_top_TM_IDDQ();
    wrapper.run_test_top_TM_IDDQ();
  endtask

  task run_test_top_TM_RAM_BIST_result();
    wrapper.run_test_top_TM_RAM_BIST_result();
  endtask

  task run_test_top_TM_RAM_BIST_start();
    wrapper.run_test_top_TM_RAM_BIST_start();
  endtask

  task run_test_top_TM_SCAN();
    wrapper.run_test_top_TM_SCAN();
  endtask

  task run_test_top_TM_SCAN_COMPR();
    wrapper.run_test_top_TM_SCAN_COMPR();
  endtask

  task run_OTP_MISSION_LEAKY();
    wrapper.run_OTP_MISSION_LEAKY();
  endtask

  task run_OTP_MISSION_WEAK();
    wrapper.run_OTP_MISSION_WEAK();
  endtask

  task run_Clock_CLKREF();
    wrapper.run_Clock_CLKREF();
  endtask

  function automatic void set_time_value_sets(value_set_e value_set);
    wrapper.set_value_set(value_set);
  endfunction

  initial begin
    wrapper = new(connector);
  end
endmodule
