// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Parse Vector File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : parse_vector.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class parse_vector;
  protected string vector;
  protected string vector_elements[$];
  protected int index;

  function new();
  endfunction

  static function parse_vector create(string vector);
    parse_vector new_vector;
    new_vector = new();
    new_vector.initialize(vector);
    return new_vector;
  endfunction

  function void initialize(string vector);
    this.vector = vector;
    get_vector_elements(this.vector);
    index = 0;
  endfunction

  function void get_vector_elements(string vector);
    string current_vector;
    current_vector = vector;
    while (current_vector.match("[sc]\\d+:[a-zA-Z0-9_]+|D0|D1|DZ|EL|EH|EX|EZ|EM|EV")>0) begin
      vector_elements.push_back(current_vector.thismatch());
      current_vector = remove_leading_colon(current_vector.postmatch());
    end
  endfunction

  virtual function string remove_leading_colon(string line);
    if (line.match("^\\s*,\\s*(.*)"))
      return line.backref(0);
    else return line;
  endfunction

  virtual function bit has_next();
    if (index < vector_elements.size) return 1'b1;
      return 1'b0;
  endfunction

  virtual function void next();
    index++;
  endfunction

  virtual function string get_element();
    return vector_elements[index];
  endfunction

  virtual function bit is_variable();
    if (vector_elements[index].match("([sc])(\\d+):(.*)") > 0) return 1'b1;
    return 1'b0;
  endfunction

  virtual function string get_variable_name();
    if (is_variable()) begin
      return vector_elements[index].backref(2);
    end
    return "";
  endfunction

  virtual function int get_variable_bit_position();
    if (is_variable()) begin
      return vector_elements[index].backref(1).atoi();
    end
    return 0;
  endfunction

  virtual function io_def_t get_io_definition();
    if (!is_variable()) begin
      io_def_t io_def;
      io_def = io_def.first();
      do begin
        if (io_def.name() == vector_elements[index])
          return io_def;
        io_def = io_def.next();
      end while (io_def != io_def.first);
    end
    else begin
      if (is_capture_variable())
        return CAPTURE;
      if (is_source_variable())
        return SOURCE;
    end
    return NONE;
  endfunction

  virtual function bit is_capture_variable();
    if (vector_elements[index].match("([c])(\\d+):(.*)") > 0) return 1'b1;
      return 1'b0;
  endfunction

  virtual function bit is_source_variable();
    if (vector_elements[index].match("([s])(\\d+):(.*)") > 0) return 1'b1;
    return 1'b0;
  endfunction
endclass
