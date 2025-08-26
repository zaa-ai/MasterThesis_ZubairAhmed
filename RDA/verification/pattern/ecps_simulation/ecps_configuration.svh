// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Configuration File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : ecps_configuration.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 7, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class ecps_configuration;
  protected integer source_variables[string];
  protected integer capture_variables[string];
  protected string current_timeplate;

  static protected ecps_configuration configuration;

  protected log_handler _log_handler;

  protected function new();
    source_variables.delete();
    capture_variables.delete();
    current_timeplate = "";
    _log_handler = default_log_handler::create();
  endfunction

  static function ecps_configuration get_configuration();
    if (configuration == null)
      configuration = new();
    return configuration;
  endfunction

  static function void set_source_variable(string name, int value);
    ecps_configuration configuration;
    configuration = get_configuration();
    configuration.source_variables[name] = value;
  endfunction

  static function integer get_source_variable(string name);
    ecps_configuration configuration;
    configuration = get_configuration();
    return configuration.source_variables[name];
  endfunction

  static function logic get_source_variable_bit(string name, int bit_position);
    ecps_configuration configuration;
    configuration = get_configuration();
    if (!configuration.source_variables.exists(name)) begin
      configuration.source_variables[name] = 'bx;
      configuration._log_handler.report_error($sformatf("variable with name %s does not exist in configuration! Please, add the variable in the configuration.", name),,`__FILE__, `__LINE__);
    end
    return configuration.source_variables[name][bit_position];
  endfunction

//  static function void set_capture_variable(string name, int value);
//    ecps_configuration configuration;
//    configuration = get_configuration();
//    configuration.capture_variables[name] = value;
//  endfunction

  static function integer get_capture_variable(string name);
    ecps_configuration configuration;
    configuration = get_configuration();
    if (!configuration.capture_variables.exists(name)) begin
      configuration.capture_variables[name] = 0;
      configuration._log_handler.report_error($sformatf("variable with name %s does not exist in configuration! It seems, that the variable does not exist in the pattern.", name),,`__FILE__, `__LINE__);
    end
    return configuration.capture_variables[name];
  endfunction

  static function void set_capture_variable_bit(string name, int bit_position, logic value);
    if(configuration == null)
      configuration = new();
    if (!configuration.capture_variables.exists(name)) begin
      configuration.capture_variables[name] = 0;
      configuration._log_handler.report_warning($sformatf("variable with name %s does not exist in configuration! The %s was set to 0.", name, name));
    end
    configuration.capture_variables[name][bit_position] = value;
  endfunction

  static function void set_current_timeplate(string timeplate);
    ecps_configuration configuration;
    configuration = get_configuration();
    configuration.current_timeplate = timeplate;
  endfunction

  static function string get_current_timeplate();
    ecps_configuration configuration;
    configuration = get_configuration();
    return configuration.current_timeplate;
  endfunction

  static function log_handler get_log_handler();
    ecps_configuration configuration;
    configuration = get_configuration();
    return configuration._log_handler;
  endfunction
endclass
