// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Vector File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : ecps_pattern_vector.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class ecps_pattern_vector extends log_object implements pattern_element;
  protected vector_element signal_values[$];
  protected int repeats;
  ecps_configuration configuration;

  function new();
    signal_values.delete();
    repeats = 1;
    configuration = ecps_configuration::get_configuration();
  endfunction

  virtual function void parse(pattern_line line);
    int matched_items;
    string vector;

    matched_items = $sscanf(line.line, "%d,%s", repeats, vector);
    if (matched_items != 2) begin
      line.line = "";
      return;
    end

    begin
      parse_vector vector_iterator;
      vector_iterator = parse_vector::create(vector);
      while (vector_iterator.has_next()) begin
        vector_element element;
        element = new(vector_iterator.get_io_definition(), vector_iterator.get_variable_name(), vector_iterator.get_variable_bit_position());
        if (element.value == NONE) begin
          error($sformatf("no definition found for %s in line %d", vector_iterator.get_element(), line.get_line_number()));
        end
        else
          signal_values.push_back(element);
        vector_iterator.next();
      end
    end
    line.line = "";
  endfunction

  static function bit add(pattern_line line, ref pattern_element elements[$]);
    ecps_pattern_vector vector;
    vector = new();
    vector.parse(line);
    if (vector.has_value()) begin
      elements.push_back(vector);
      return 1'b1;
    end
    else return 1'b0;
  endfunction

  virtual function bit has_value();
    if (signal_values.size()==0) return 1'b0;
    else return 1'b1;
  endfunction

  virtual task execute(pattern_connector connector);
    get_variable_values_from_configuration();
    repeat(repeats) begin
      connector.apply_vector(signal_values);
    end
    set_variable_values_in_configuration();
  endtask

  protected virtual function void get_variable_values_from_configuration();
    foreach (signal_values[i]) begin
      if (signal_values[i].value == SOURCE) begin
        logic   value_from_configuration;
        value_from_configuration = configuration.get_source_variable_bit(signal_values[i].variable_name, signal_values[i].bit_position);
        signal_values[i].value = get_io_definition(value_from_configuration);
      end
    end
  endfunction

  protected virtual function void set_variable_values_in_configuration();
    foreach (signal_values[i]) begin
      if (signal_values[i].value == CAPTURE) begin
        configuration.set_capture_variable_bit(signal_values[i].variable_name, signal_values[i].bit_position, signal_values[i].return_value);
      end
    end
  endfunction
endclass
