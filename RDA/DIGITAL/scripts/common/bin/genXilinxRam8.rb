#!/usr/bin/env ruby

#param0: output filename
#param1: entity name
#param2: addr_width
#param3: init hex file (optional)
#param4: byte row offset (only if param3 set)
#param5: fill ram with FF (optional)

def toBinString(no, len)
  l   = no;
  ret = "";
  (1..len).each{|i|
    if (l % 2 == 0)
      ret = "0"+ret;
    else
      ret = "1"+ret;
    end
    l /= 2;
  }
  ret
end

def toHexString(no, len)
  l   = no;
  ret = "";
  (1..len).each{|i|
    x = l % 16;
    case (x)
      when 0..9 then ret = "#{x}"+ret;
      when   10 then ret = "A"+ret;
      when   11 then ret = "B"+ret;
      when   12 then ret = "C"+ret;
      when   13 then ret = "D"+ret;
      when   14 then ret = "E"+ret;
      when   15 then ret = "F"+ret;
    end
    l /= 16;
  }
  ret
end

def toDecString(no, len)
  l = no;
  ret = "";
  (1..len).each{|i|
    ret = "#{l % 10}"+ret;
    l /= 10;
  }
  ret
end
  

# generate RAM file
file_name       = ARGV[0];
entity_name     = ARGV[1];
addr_width      = ARGV[2].to_i;

ram_addr_width  = 11;
ram_type        = "RAMB16";
ram_port        = "S9";
ram_name        = ram_type+"_"+ram_port;
no_of_rams      = 2**(addr_width-ram_addr_width);
if (no_of_rams < 1)
  no_of_rams = 1
end
init_style      = 1;

puts "file_name: #{file_name}";
puts "entity_name: #{entity_name}";
puts "addr_width: #{addr_width}";
puts "=> selected ram";
puts "ram_name: #{ram_name}";
puts "ram_addr_width: #{ram_addr_width}";
puts "no_of_rams: #{no_of_rams}";
case init_style
when 1
  puts "init_style: synplify";
when 2
  puts "init_style: synopsys";
when 3
  puts "init_style: precision";
when 4
  puts "init_style: rtl compiler";
end

file_content  = "";
file_content += "\n";
file_content += "`timescale 1ns/1ns\n";
file_content += "\n";
file_content += "module #{entity_name} (\n";
file_content += "\t\tinput              clk,\n";
file_content += "\t\tinput              sp_write,\n";
file_content += "\t\tinput      [#{addr_width-1}:0]  sp_addr,\n";
file_content += "\t\tinput       [7:0]  sp_din,\n";
file_content += "\t\toutput reg  [7:0]  sp_dout\n";
file_content += "\t);\n";
file_content += "\n";
file_content += "\treg  [#{ram_addr_width-1}:0] s_addr;\n";
file_content += "\n";

(0..no_of_rams-1).each{|i|
  file_content += "\t// bank #{i}\n";
  file_content += "\treg         s_bank#{i}_write;\n";
  file_content += "\twire  [7:0] s_bank#{i}_dout;\n";
  file_content += "\twire        s_bank#{i}_open_DOP;\n";
  file_content += "\n";

  file_content += "\t#{ram_name} bank#{i} (\n";
  file_content += "\t\t.DO(s_bank#{i}_dout),\n";
  file_content += "\t\t.DOP(s_bank#{i}_open_DOP),\n";
  file_content += "\t\t.ADDR(s_addr),\n";
  file_content += "\t\t.CLK(clk),\n";
  file_content += "\t\t.DI(sp_din),\n";
  file_content += "\t\t.DIP(1'b0),\n";
  file_content += "\t\t.EN(1'b1),\n";
  file_content += "\t\t.SSR(1'b0),\n";
  file_content += "\t\t.WE(s_bank#{i}_write)\n";
  file_content += "\t);\n";
  file_content += "\n";
}

if (no_of_rams > 1)
  file_content += "\t// dout sel\n";
  file_content += "\treg [#{addr_width-1}:#{ram_addr_width}] s_dout_sel;\n";
  file_content += "\n";
  file_content += "\talways @(posedge clk)\n";
  file_content += "\tbegin\n";
  file_content += "\t\ts_dout_sel <= sp_addr[#{addr_width-1}:#{ram_addr_width}];\n";
  file_content += "\tend\n";
  file_content += "\n";

  file_content += "\t// write gen and bank sel\n";
  file_content += "\talways @*\n";
  file_content += "\tbegin\n";
  file_content += "\t\ts_addr = #{ram_addr_width}'d0;\n";
    used_addr_width = (ram_addr_width < addr_width) ? ram_addr_width : addr_width  # min value of both address width values
  file_content += "\t\ts_addr[#{used_addr_width-1}:0] = sp_addr[#{used_addr_width-1}:0];\n";
  file_content += "\n";
  (0..no_of_rams-1).each{|i|
    file_content += "\t\ts_bank#{i}_write = 1'b0;\n";
  }
  file_content += "\t\tcase (sp_addr[#{addr_width-1}:#{ram_addr_width}])\n";
  (0..no_of_rams-1).each{|i|
    file_content += "\t\t\t#{addr_width-ram_addr_width}'b#{toBinString(i, addr_width-ram_addr_width)}: s_bank#{i}_write = sp_write;\n";
  }
  file_content += "\t\tendcase\n";
  file_content += "\n";
  file_content += "\t\tsp_dout = s_bank0_dout;\n";
  file_content += "\t\tcase (s_dout_sel)\n";
  (0..no_of_rams-1).each{|i|
    file_content += "\t\t\t#{addr_width-ram_addr_width}'b#{toBinString(i, addr_width-ram_addr_width)}: sp_dout = s_bank#{i}_dout;\n";
  }
  file_content += "\t\tendcase\n";
  file_content += "\tend\n";
  file_content += "\n";
else
  file_content += "\talways @(*)\n";
  file_content += "\tbegin\n";
  file_content += "\t\ts_addr = #{ram_addr_width}'d0;\n";
  file_content += "\t\ts_addr[#{addr_width-1}:0] = sp_addr;\n";
  file_content += "\t\tsp_dout = s_bank0_dout;\n";
  file_content += "\t\ts_bank0_write = sp_write;\n";
  file_content += "\tend\n";
  file_content += "\n";
end

# RAM init values
init_hex_file   = ARGV[3]
hex_byte_offset = ARGV[4]
fill_with_FF    = ARGV[5]

if (!init_hex_file.nil?)
  byte_offset     = hex_byte_offset.to_i
  ram_init_lines  = (2**ram_addr_width/32)
  ram_init_rows   = 256;
  hex_file_content = IO.readlines(init_hex_file)
  puts "=> using init file";
  puts "hex file name: #{init_hex_file}";
  puts "byte row offset: #{byte_offset}";
  puts "found hex lines: #{hex_file_content.length}";
  
  ram_content = Array.new();
  n = 0;
  s = "";
  (0..hex_file_content.length-1).each{ |l|
    if (n == 0)
      n = ram_init_rows/8;
    end
    s = hex_file_content[l][byte_offset*2 .. byte_offset*2+1].strip + s;
    n -= 1;
    if (n == 0)
      ram_content << s;
      s = "";
    end
  }
  while (n > 0)
    s = "00" + s;
    n -= 1;
    if (n == 0)
      ram_content << s;
    end
  end
  puts "found #{ram_content.length} lines"
  puts "each block takes #{ram_init_lines} INIT lines"
  
  fill_content = ""
  (0..ram_init_rows/8-1).each{ 
    fill_content += "FF"
  }
  if (!fill_with_FF.nil?) and (fill_with_FF.to_i == 1)
    puts "filling RAM with FF after INIT"
  end
  
  # for Synopsys
  if (init_style == 2)
    file_content += "\t//synopsys dc_script_begin\n";
    cl = 0;
    (0..no_of_rams-1).each{|i|
      (0..ram_init_lines-1).each{|l|
        if (cl < ram_content.length)
          file_content += "\t//set_attribute bank#{i} INIT_#{toHexString(l,2)} \"#{ram_content[cl]}\" -type string\n";
          cl += 1;
        elsif (!fill_with_FF.nil?) and (fill_with_FF.to_i == 1)
          file_content += "\t//set_attribute bank#{i} INIT_#{toHexString(l,2)} \"#{fill_content}\" -type string\n";
        end
      }
    }
    file_content += "\t//synopsys dc_script_end\n";
    file_content += "\n";
  end

  # for RTL COMPILER
  if (init_style == 4)
    file_content += "\t//synopsys dc_script_begin\n";
    cl = 0;
    (0..no_of_rams-1).each{|i|
      (0..ram_init_lines-1).each{|l|
        if (cl < ram_content.length)
          file_content += "\t//set_user_attribute INIT_#{toHexString(l,2)} \"#{ram_content[cl]}\" bank#{i}\n";
          cl += 1;
        elsif (!fill_with_FF.nil?) and (fill_with_FF.to_i == 1)
          file_content += "\t//set_user_attribute INIT_#{toHexString(l,2)} \"#{fill_content}\" bank#{i}\n";
        end
      }
    }
    file_content += "\t//synopsys dc_script_end\n";
    file_content += "\n";
  end

  # for Precision
  if (init_style == 3)
    cl = 0;
    (0..no_of_rams-1).each{|i|
      (0..ram_init_lines-1).each{|l|
        if (cl < ram_content.length)
          file_content += "\t//pragma attribute bank#{i} INIT_#{toHexString(l,2)} #{ram_content[cl]}\n";
          cl += 1;
        elsif (!fill_with_FF.nil?) and (fill_with_FF.to_i == 1)
          file_content += "\t//pragma attribute bank#{i} INIT_#{toHexString(l,2)} #{fill_content}\n";
        end
      }
    }
    file_content += "\n";
  end

  # for Simulation / Synplify
  if (init_style != 1)
    file_content += "\t//synopsys translate_off\n";
  end
  cl = 0;
  (0..no_of_rams-1).each{|i|
    (0..ram_init_lines-1).each{|l|
      if (cl < ram_content.length)
        file_content += "\tdefparam bank#{i}.INIT_#{toHexString(l,2)} = #{ram_init_rows}'h#{ram_content[cl]};\n";
        cl += 1;
      elsif (!fill_with_FF.nil?) and (fill_with_FF.to_i == 1)
        file_content += "\tdefparam bank#{i}.INIT_#{toHexString(l,2)} = #{ram_init_rows}'h#{fill_content};\n";
      end
    }
  }
  if (init_style != 1)
    file_content += "\t//synopsys translate_on\n";
  end
  file_content += "\n";

end

file_content += "endmodule";

File.open(file_name, "w") { |file|
   file << file_content;
}

