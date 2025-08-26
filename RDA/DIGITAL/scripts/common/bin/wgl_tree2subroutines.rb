#!/usr/bin/env ruby

# ========================================================================== #
# This program is free software: you can redistribute it and/or modify       #
# it under the terms of the GNU General Public License as published by       #
# the Free Software Foundation, either version 3 of the License, or          #
# (at your option) any later version.                                        #
#                                                                            #
# This program is distributed in the hope that it will be useful,            #
# but WITHOUT ANY WARRANTY; without even the implied warranty of             #
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              #
# GNU General Public License for more details.                               #
#                                                                            #
# You should have received a copy of the GNU General Public License          #
# along with this program.  If not, see <http://www.gnu.org/licenses/>.      #
#                                                                            #
# Dieses Programm ist Freie Software: Sie können es unter den Bedingungen    #
# der GNU General Public License, wie von der Free Software Foundation,      #
# Version 3 der Lizenz oder (nach Ihrer Wahl) jeder neueren                  #
# veröffentlichten Version, weiterverbreiten und/oder modifizieren.          #
#                                                                            #
# Dieses Programm wird in der Hoffnung, dass es nützlich sein wird, aber     #
# OHNE JEDE GEWÄHRLEISTUNG, bereitgestellt; sogar ohne die implizite         #
# Gewährleistung der MARKTFÄHIGKEIT oder EIGNUNG FÜR EINEN BESTIMMTEN ZWECK. #
# Siehe die GNU General Public License für weitere Details.                  #
#                                                                            #
# Sie sollten eine Kopie der GNU General Public License zusammen mit diesem  #
# Programm erhalten haben. Wenn nicht, siehe <http://www.gnu.org/licenses/>. #
# ========================================================================== #

require 'fileutils'
require 'rexml/document'
include REXML

$file_content   = Array.new
$call_labels    = Hash.new   # to accelerate $file_content parse
$wgl_timeplates = Array.new

# =======================================================

class WglTimeplate

  attr_accessor :signals

  def initialize(name, period, sample)
    @name    = String.new(name)
    @period  = period.to_i
    @sample  = sample.to_i
    @signals = Array.new
  end

  def to_signals_s
    ret = ""
    ret += "  signal\n"
    @signals.each { |s|
      ret += s.to_signal_s
    }
    ret += "  end\n"
  end

  def to_s
    ret = ""
    ret += "  timeplate #{@name} period #{@period}ns\n"
    @signals.each { |s|
      ret += s.to_timeplate_s(@period, @sample)
    }
    ret += "  end\n"
  end
end

# =======================================================

class WglSignal

  attr_accessor :name, :type

  INPUT  = 0
  OUTPUT = 1
  BIDIR  = 2

  def initialize(name, type, is_clock=false, const=nil)
    @name     = String.new(name)
    @type     = type
    @is_clock = is_clock
    @const    = const     # nil, 0, 1
  end

  def to_signal_s
    ret = ""
    if @type == INPUT
      ret += "    \"#{@name}\" : input  initialp[N];\n"
    end
    if @type == OUTPUT
      ret += "    \"#{@name}\" : output;\n"
    end
    if @type == BIDIR
      ret += "    \"#{@name}\" : bidir  initialp[N];\n"
    end
    ret
  end

  def to_timeplate_s(period, sample)
    ret = ""
    if @is_clock
      ret += "    \"#{@name}\" := input[0ns:S, #{period.to_i/2}ns:U];\n"
    else
      if @type == INPUT
        ret += "    \"#{@name}\" := input[0ns:S];\n"
      end
      if @type == OUTPUT
        ret += "    \"#{@name}\" := output[0ns:X, #{sample}ns:Q, #{sample.to_i+2}ns:X];\n"
      end
      if @type == BIDIR
        ret += "    \"#{@name}\" := input[0ns:S];\n"
        ret += "    \"#{@name}\" := output[0ns:X, #{sample}ns:Q, #{sample.to_i+2}ns:X];\n"
      end
    end
    ret
  end
end

# =======================================================

class WglSubroutine

  attr_accessor :name, :content, :level, :used_as_pattern, :short_name

  def initialize(name)
    @name    = String.new(name)
    @content = Array.new
    @level   = 0
    @used_as_pattern = false  # top level functions ("WGL pattern")
    @short_name = ""
  end

  def parse
    @content = Array.new
    inside = false
    clevel = 0;
    flevel = 0;
    $file_content[$call_labels[@name]..$file_content.length-1].each { |line|
      line.sub!(/^\s*\d+ ms : /, "")
      if line =~ /^\s*(\d+) - /
        clevel = $1.to_i
      end
      if inside
        if clevel <= flevel
          return
        else
          if clevel == (flevel + 1)
            if line =~ /^\s*\d+ - (.+)\s*$/
              @content << $1
            end
          end
        end
      else
        if line =~ /^\s*(\d+) - .*\b#{@name}\b/
          inside = true
          flevel = $1.to_i
        end
      end
    }
  end

  def to_wgl
    ret = ""
    ret += "  {#{@name}}\n"
    ret += "  subroutine #{@short_name}()\n"
    @content.each { |c|
      ret += "    #{c}\n"
    }
    ret += "  end\n\n"
    ret
  end
end

# =======================================================

class WglSubroutines

  def initialize(start_bin)
    @start_bin = start_bin.to_i
    @subroutines = Array.new
  end

  def include?(name)
    @subroutines.each { |s|
      if s.name == name
        return true
      end
    }
    false
  end

  def update_level(name, level)
    @subroutines.each { |s|
      if s.name == name
        if s.level < level
          s.level = level
        end
        if level == 0
          s.used_as_pattern = true
        end
        return
      end
    }
  end

  def get_short_name(name)
    @subroutines.each { |s|
      if s.name == name
        return s.short_name
      end
    }
    ""
  end

  def base_name_used_once?(name)
    base_name = String.new(name)
    base_name.sub!(/__.+/, "")

    n = 0
    @subroutines.each { |s|
      bn = String.new(s.name)
      bn.sub!(/__.+/, "")
      if bn == base_name
        n = n + 1
      end
    }
    if n > 1
      return false
    end
    true
  end

  def set_short_names

    # used here to make different test-step pattern names unique ;-) ...
    # times 10 to extend space to next used unique name area ...
    n = @start_bin*10;

    @subroutines.each { |s|
      s.short_name = String.new(s.name)

      # start_bin == 0 means general purpose wgl ...
      if (@start_bin == 0) and base_name_used_once?(s.name)
        s.short_name.sub!(/__.+/, "")
      else
        # append a unique number only if function "base name" appears
        # more than once in @subroutines and (start_bin != 0) ...

        if s.short_name =~ /__.+/
          s.short_name.sub!(/__.+/, "_#{n}")
        else
          s.short_name = "#{s.short_name}_#{n}"
        end
      end
      n = n+1
    }
    @subroutines.each { |s|
      s.content.each { |c|
        if c =~ /call \b(\w+)\b/i
          c.sub!(/call \b\w+\b/i, "call #{get_short_name($1)}")
        end
      }
    }
  end

  def parse
    $file_content.each_index { |n|
      line = $file_content[n]
      line.sub!(/^\s*\d+ ms : /, "")
      if line =~ /^\s*(\d+) - call \b(\w+)\b/i
        if $call_labels[$2].nil?
          $call_labels[$2] = n
        end
        level = $1.to_i
        name  = $2
        if !include?(name)
          s = WglSubroutine.new(name)
          s.level = level
          if level == 0
            s.used_as_pattern = true
          end
          @subroutines << s
        else
          update_level(name, level)
        end
      end
    }

    sort_by_name!

    @subroutines.each { |s|
      puts "parsing #{s.name} ..."
      s.parse
    }

    set_short_names
  end

  def sort_by_name!
    @subroutines.replace(@subroutines.sort { |a, b|
      a.name <=> b.name
    })
  end

  def sort_by_level!
    @subroutines.replace(@subroutines.sort { |a, b|
      if a.level == b.level
        a.name <=> b.name
      else
        b.level <=> a.level  # highest level first !
      end
    })
  end

  # ============= WGL ===============

  def to_wgl_header(name)
    ret = ""
    ret += "waveform #{name}_wave\n"
    ret += "\n"

    ret += $wgl_timeplates.first.to_signals_s

    $wgl_timeplates.each { |tp|
      ret += tp.to_s
    }
    ret += "\n"
    ret
  end

  def to_wgl_pattern
    ret = ""
    @subroutines.each { |s|
      if s.used_as_pattern
        ret += "  pattern p_#{s.short_name}("
        first = true
        $wgl_timeplates.first.signals.each { |ts|
          if !first
            ret += ", "
          end
          if ts.type == WglSignal::BIDIR
            ret += "\"#{ts.name}\":I, \"#{ts.name}\":O"
          else
            ret += "\"#{ts.name}\""
          end
          first = false
        }
        ret += ")\n"
        ret += "    call #{s.short_name}();\n"
        ret += "  end\n"
        ret += "\n"
      end
    }
    ret
  end

  def to_wgl_footer
    ret = ""
    ret += "end\n"
    ret += "\n"
    ret
  end

  def to_wgl(name)
    ret = ""
    ret += "\n"
    ret += to_wgl_header(name)
    ret += to_wgl_pattern
    @subroutines.each { |s|
      ret += s.to_wgl
    }
    ret += to_wgl_footer
    ret
  end

  # ============= C ===============

  def to_c_test_header(name)
    ret = ""
    ret += "\n"
    ret += "void TS_#{name.upcase}(void) {\n"
    ret += "\n"
    ret += "  // TODO change to useful values ... !\n"
    ret += "  int anabin = 0;\n"
    ret += "  const char *pattern_name = \"my_pattern_name\";\n"
    ret += "\n"
    ret
  end

  def to_c_test_footer
    ret = ""
    ret += "}\n"
    ret += "\n"
    ret
  end

  def to_c_pattern_call(name, n)
    ret = ""
    ret += "  MY_PATTERN_EVAL(#{n}, pattern_name, \"p_#{name}\");\n"
    ret += "\n"
    ret
  end

  def to_c_supply_set(name, value)
    ret = ""
    ret += "  MY_SUPPLY_SET_#{name}(#{value});\n"
    ret += "\n"
    ret
  end

  def to_c(name)
    ret = ""
    ret += to_c_test_header(name)

    n = @start_bin
    $file_content.each { |line|
      line.sub!(/^\s*\d+ ms : /, "")
      if line =~ /^\s*#\s*(.*)/
        ret += "  // #{$1}\n"
      end
      if line =~ /^\s*CODE\s*(.*)/
        code = $1;
        if code =~ /\bBIN\b/
          code.sub!(/\bBIN\b/, "#{n}")
          n = n+2
        end
        ret += "  #{code}\n"
      end
      if line =~ /^\s*0 - call (.*)\(\);/
        ret += to_c_pattern_call(get_short_name($1), n)
        n = n+2
      end
      if line =~ /^\s*0 - VDDIO = (\d+)/
        ret += to_c_supply_set("VDDIO", $1.to_f/10.0)
      end
      if line =~ /^\s*0 - VDDC = (\d+)/
        ret += to_c_supply_set("VDDC", $1.to_f/10.0)
      end
      if line =~ /^\s*0 - VPP = (\d+)/
        ret += to_c_supply_set("VPP", $1.to_f/10.0)
      end
    }

    ret += to_c_test_footer
    ret
  end

  # ============= Credence ===============

  def to_credence_test_header(name)
    ret = ""
    ret += "\n"
    ret += "--------------------------------------------------------------------------------\n"
    ret += "procedure TS_#{name.upcase}\n"
    ret += "--------------------------------------------------------------------------------\n"
    ret += "\n"
    ret += "local\n"
    ret += "\n"
    ret += "end_local\n"
    ret += "\n"
    ret += "body\n"
    ret += "\n"
    ret
  end

  def to_credence_test_footer
    ret = ""
    ret += "end_body\n"
    ret += "\n"
    ret
  end

  def to_credence_pattern_call(name, n)
    ret = ""
    # after compile of multiple flat (one file per pattern) WGL - filename and pattern
    # name are combined to new pattern name ...
    ret += "  MY_PATTERN_EVAL(#{n}, \"p_#{name}\")\n"
    ret += "\n"
    ret
  end

  def to_credence_supply_set(name, value)
    ret = ""
    ret += "  MY_SUPPLY_SET_#{name}(#{value})\n"
    ret += "\n"
    ret
  end

  def to_credence(name)
    ret = ""
    ret += to_credence_test_header(name)

    n = @start_bin
    $file_content.each { |line|
      line.sub!(/^\s*\d+ ms : /, "")
      if line =~ /^\s*#\s*(.*)/
        ret += "  -- #{$1}\n"
      end
      if line =~ /^\s*CODE\s*(.*)/
        code = $1;
        if code =~ /\bBIN\b/
          code.sub!(/\bBIN\b/, "#{n}")
          n = n+2
        end
        ret += "  #{code.sub!(/;/, "")}\n"  # skip semicolon from CODE line
      end
      if line =~ /^\s*0 - call (.*)\(\);/
        ret += to_credence_pattern_call(get_short_name($1), n)
        n = n+2
      end
      if line =~ /^\s*0 - VDDIO = (\d+)/
        ret += to_credence_supply_set("VDDIO", $1.to_f/10.0)
      end
      if line =~ /^\s*0 - VDDC = (\d+)/
        ret += to_credence_supply_set("VDDC", $1.to_f/10.0)
      end
      if line =~ /^\s*0 - VPP = (\d+)/
        ret += to_credence_supply_set("VPP", $1.to_f/10.0)
      end
    }

    ret += to_credence_test_footer
    ret
  end

end

# =======================================================

class WglXMLConfig

  def initialize(file_name)
    @file_name = String.new(file_name)
  end

  def parse
    if File.exists?(@file_name)
      xml = REXML::Document.new(File.open(@file_name, "r"))

      signals = Array.new

      XPath.match(xml, "/config/signal").each { |node|
        name = ""
        if XPath.match(node, "name").length > 0
          name = XPath.first(node, "name").text.strip
        else
          # TODO no name error puts and exit
        end
        type = WglSignal::INPUT
        if XPath.match(node, "type").length > 0
          if XPath.first(node, "type").text.strip == "input"
            type = WglSignal::INPUT
          end
          if XPath.first(node, "type").text.strip == "output"
            type = WglSignal::OUTPUT
          end
          if XPath.first(node, "type").text.strip == "bidir"
            type = WglSignal::BIDIR
          end
        else
          # TODO no type error puts and exit
        end
        is_clock = false
        if XPath.match(node, "is_clock").length > 0
          if XPath.first(node, "is_clock").text.strip == "1"
            is_clock = true
          end
        end
        const = nil
        if XPath.match(node, "const").length > 0
          if XPath.first(node, "const").text.strip == "0"
            const = 0
          else
            const = 1
          end
        end
        signals << WglSignal.new(name, type, is_clock, const)
      }

      XPath.match(xml, "/config/timeplate").each { |node|
        name = ""
        if XPath.match(node, "name").length > 0
          name = XPath.first(node, "name").text.strip
        else
          # TODO no name error puts and exit
        end
        period = 1000
        if XPath.match(node, "period").length > 0
          period = XPath.first(node, "period").text.strip.to_i
        else
          # TODO no period error puts and exit
        end
        sample = 900
        if XPath.match(node, "sample").length > 0
          sample = XPath.first(node, "sample").text.strip.to_i
        else
          # TODO no sample error puts and exit
        end

        tp = WglTimeplate.new(name, period, sample)
        tp.signals = signals
        $wgl_timeplates << tp
      }
    else
      puts "\n"
      puts "  >>>> ERROR: Missing XML config file \"#{@file_name}\" !\n"
      puts "\n"
      exit 1
    end
  end

end

# =======================================================

if ARGV.length != 2
  STDERR.puts "USAGE: #{$0} <start-bin> <base-name>\n"
  exit 1
end

start_bin = ARGV[0].to_i     # "sort" start bin
base_name = ARGV[1]          # file base name

# =======================================================

file_name_r = "#{base_name}.log"    # input file
file_name_w = "#{base_name}.wgl"    # WGL subroutines output file
file_name_c = "#{base_name}.c"      # level 0 calls C output file
file_name_m = "#{base_name}.mod"    # level 0 calls Credence output file

# =======================================================

xml = WglXMLConfig.new("wgl_config.xml")
xml.parse

# =======================================================

puts "==== LOG FILE READ ===="

$labels = Array.new
lines = 0

File.open(file_name_r, 'r') { |f|
  level = nil
  skip = false
  while line = f.gets
    if lines & 0xFFFF == 0  # ... show progress
      print "."
    end
    lines = lines + 1

    sline = String.new(line)
    sline.sub!(/^\s*\d+ ms : /, "")

    if sline =~ /^\s*(\d+) - /
      if !level.nil? and ($1.to_i <= level.to_i)
        level = nil
        skip = false
      end
      if sline =~ /^\s*(\d+) - \s*V/
        if $1.to_i > 0
          # voltage changes have to take place at level 0 because they have to be done
          # by tester program (level 0) and cannot be done by pattern (higher levels) ...
          puts "ERROR: Input log file includes voltage change at call-level > 0 !\n"
          exit 1
        end
      end
    end

    if !skip or (sline =~ /^\s*#/) or (sline =~ /^\s*CODE\b/)
      $file_content << line

      if sline =~ /^\s*(\d+) - call (\w+)\(\);/i
        if $labels.include?($2)
          level = $1.to_i
          # skip repeated (known) call hierarchy content to speed up parsing
          skip = true
        else
          $labels << String.new($2)
        end
      end
    end
  end
}

puts ""
puts "log file lines : #{lines}"
puts "lines to parse : #{$file_content.length}"

# =======================================================

puts "==== PARSE ===="

srs = WglSubroutines.new(start_bin)
srs.parse
srs.sort_by_level!

# =======================================================

puts "==== WGL GENERATE ===="

File.open(file_name_w, "w") { |fw|
  fw << srs.to_wgl(base_name)
}

puts "==== C GENERATE ===="

File.open(file_name_c, "w") { |fc|
  fc << srs.to_c(base_name)
}

puts "==== CREDENCE GENERATE ===="

File.open(file_name_m, "w") { |fm|
  fm << srs.to_credence(base_name)
}

# =======================================================

puts "==== FINISHED ===="

