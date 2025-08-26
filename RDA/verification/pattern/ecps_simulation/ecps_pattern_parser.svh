// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Parser File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : pattern_parser.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 7, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class ecps_pattern_parser implements parser;
  protected int           file_id;
  protected int           line_number;

  function new();
  endfunction

  virtual task parse(string file_name, pattern_connector connector);
    pattern_line line;
    line_number = 0;
    open_file(file_name);
    while(has_next()) begin
      pattern_element elements[$];
      line = get_line();
      if (line != null) begin
        while (~line.is_empty()) begin
          void'(ecps_pattern_linenumber::add(line, elements));
          void'(ecps_pattern_comment::add(line, elements));
          void'(ecps_pattern_timeplate::add(line, elements));
          void'(ecps_pattern_vector::add(line, elements));
        end
        while (elements.size()>0) begin
          elements[0].execute(connector);
          elements.delete(0);
        end
      end
    end
    stop_parsing();
  endtask

  protected virtual function pattern_line get_line();
    string line;
    int code;
    do begin
      if (!is_eof()) begin
        code = $fgets(line, file_id);
        line_number++;
      end
      else return null;
    end while (code <= 1);
    get_line = new(line, line_number);
  endfunction

  virtual function bit is_eof();
    if (file_id != 0)
      return $feof(file_id);
    return 1'b1;
  endfunction

  virtual function bit has_next();
    return ~is_eof();
  endfunction

  protected virtual function void open_file(string file_name);
    file_id = $fopen(file_name, "r");
    line_number = 0;
  endfunction

  virtual function void stop_parsing();
    if (file_id > 0)
      $fclose(file_id);
  endfunction

  virtual function get_line_number();
    return line_number;
  endfunction
endclass
