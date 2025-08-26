// ------------------------------------------------------------------------------
// created by ECPS-VERILOG, version 3.1.1 (14-March-2023)
// ------------------------------------------------------------------------------
// ECPS Simulation Pattern Comment File
// ------------------------------------------------------------------------------

/*------------------------------------------------------------------------------
 * File          : ecps_pattern_comment.svh
 * Project       : ecps_simulation
 * Author        : jvoi
 * Creation date : Sep 13, 2022
 * Description   :
 *------------------------------------------------------------------------------*/

class ecps_pattern_comment implements pattern_element;
  protected string comment;
  function new();
    comment = "";
  endfunction

  virtual function void parse(pattern_line line);
    if (line.line.match("^//(.*)")>0) begin
      comment = line.line.backref(0);
      line.line = "";
    end
    else begin
      if (line.line.match("//")>0) begin
        int position;
        position = line.line.search("//");
        if (position >= 0) begin
          comment = line.line.substr(position+2, line.line.len()-1);
          line.line = line.line.substr(0, position-1);
        end
      end
    end
  endfunction

  virtual function bit has_value();
    if (comment == "")
      return 1'b0;
    return 1'b1;
  endfunction

  static function bit add(pattern_line line, ref pattern_element elements[$]);
    ecps_pattern_comment pattern_comment;
    pattern_comment = new();
    pattern_comment.parse(line);
    if (pattern_comment.has_value()) begin
      elements.push_back(pattern_comment);
      return 1'b1;
    end
    else
      return 1'b0;
  endfunction

  virtual task execute(pattern_connector connector);
    connector.set_comment(comment);
  endtask
endclass
