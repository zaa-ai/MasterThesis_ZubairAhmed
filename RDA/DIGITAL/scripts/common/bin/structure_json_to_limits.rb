#!/usr/bin/env ruby

require 'json_parser'

if ARGV.length < 1
  puts "Usage: params.rb <structure-json-file>"
  exit
end

root = Json_parser.new(ARGV[0]).root

os = Array.new
os += root.get_objects("type", "EPM")

keys = Array.new
keys << "id"
keys << "name"
keys << "unit"
keys << "min"
keys << "max"

ret = ""

os.each { |o|
  ret += "3; "

  keys.each { |key|
    val = o.get_local_value(key)

    if key == "name"
      val.gsub!(/,/, "_")
      val.gsub!(/\*/, "x")
    end
    if key == "min"
      if val !~ /^[\-\d\.]+$/  # removing strange formated values
        val = ""
      end
    end
    if key == "min" or key == "max"
      val.gsub!(/,/, ".")
    end

    val.gsub!(/\s+/, "_")
    val.gsub!(/\(/, "_")
    val.gsub!(/\)/, "_")
    val.gsub!(/@/, "_at_")
    val.gsub!(/%$/, "PERCENT")
    val.gsub!(/%/, "PERCENT_")
    val.gsub!(/°C/, "degC")
    val.gsub!(/\$\$\\\\Omega\$\$/, "Ohm")
    val.gsub!(/\$\$\\\\phi\$\$/, "Phi")
    val.gsub!(/\$\$\\\\mu\$\$/, "u")
    val.gsub!(/µ/, "u")

    val.gsub!(/[_]+/, "_")
    val.gsub!(/_$/, "")
    val.gsub!(/\^\^[\w\d_]+\^\^/, "")
    val.gsub!(/_*\/_*/, "/")

    if val == "t.b.d." or val == "tbd" or val == "TBD" or val == "-"
      val = ""
    end

    if key == "name"
      ret += "#{val};".ljust(60)
    elsif key == "unit"
      ret += "#{val};".ljust(20)
    elsif key == "max" or key == "min"
      ret += "#{val};".rjust(12)
    else
      ret += "#{val};"
    end
    ret += " "
  }
  ret += "\n"
}


puts ret

