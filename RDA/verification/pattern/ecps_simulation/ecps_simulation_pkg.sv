// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Package File
// ------------------------------------------------------------------------------

`ifndef ECPS_SIMULATION_PKG
  `define ECPS_SIMULATION_PKG
  `timescale 1ns/1ps
  package ecps_simulation_pkg;

    typedef enum {
      NONE,
      SOURCE,
      CAPTURE,
      D0, // drive low
      D1, // drive high
      DZ, // drive tri-state
      EL, // expect low
      EH, // expect high
      EX, // don't care
      EM, // expect midband
      EV  // expect valid
    } io_def_t;

    function bit check(string pin_name, logic value, io_def_t expected, int vector_line);
      check = 1'b0;
      case (expected)
        EL: check = check_expected(pin_name, value, 1'b0, vector_line);
        EH: check = check_expected(pin_name, value, 1'b1, vector_line);
        EM: check = check_expected(pin_name, value, 1'bz, vector_line);
        EV: check = expect_valid(pin_name, value, vector_line);
      endcase
    endfunction

    typedef log_handler;
    typedef ecps_configuration;

    function bit check_expected(string pin_name, logic value, logic expected, int vector_line);
      if (value !== expected) begin
        log_handler _log_handler;
        _log_handler = ecps_configuration::get_log_handler();
        _log_handler.report_error($sformatf("Value at %s is wrong at vector %0d! exp. %1b but got %1b", pin_name, vector_line, expected, value),,`__FILE__, `__LINE__);
        return 1'b1;
      end
      return 1'b0;
    endfunction

    function bit expect_valid(string pin_name, logic value, int vector_line);
      if ((value !== 1'b1) && (value !== 1'b0)) begin
        log_handler _log_handler;
        _log_handler = ecps_configuration::get_log_handler();
        _log_handler.report_error($sformatf("Value at %s is not valid at vector %0d! exp. 0/1 but got %1b", pin_name, vector_line, value),,`__FILE__, `__LINE__);
        return 1'b1;
      end
      return 1'b0;
    endfunction

    function logic get_logic(io_def_t value);
      case (value)
        D0: return 1'b0;
        D1: return 1'b1;
        DZ: return 1'bz;
      endcase
      return 1'bx;
    endfunction

    function io_def_t get_io_definition(logic value);
      casex (value)
        1'b0: return D0;
        1'b1: return D1;
        1'bz: return DZ;
        default: begin
          log_handler _log_handler;
          _log_handler = ecps_configuration::get_log_handler();
          _log_handler.report_error($sformatf("logic value %1b is not defined correctly", value),,`__FILE__, `__LINE__);
        end
      endcase
    endfunction

    typedef bit[2047:0] string_equivalent;

    `include "log_handler.svh"
    `include "default_log_handler.svh"
    `include "ecps_configuration.svh"
    `include "log_object.svh"
    `include "vector_element.svh"
    `include "timing.svh"
    `include "pattern_connector.svh"
    `include "parser.svh"
    `include "pattern_line.svh"
    `include "pattern_element.svh"
    `include "parse_vector.svh"
    `include "ecps_pattern_linenumber.svh"
    `include "ecps_pattern_timeplate.svh"
    `include "ecps_pattern_comment.svh"
    `include "ecps_pattern_vector.svh"
    `include "ecps_pattern_parser.svh"
  endpackage
`endif
