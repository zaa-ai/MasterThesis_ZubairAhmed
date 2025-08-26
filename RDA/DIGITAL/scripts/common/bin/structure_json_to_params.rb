#!/usr/bin/env ruby

require 'json_parser'

if ARGV.length < 1
  puts "Usage: params.rb <structure-json-file>"
  exit
end

root = Json_parser.new(ARGV[0]).root

os = Array.new
os += root.get_objects("type", "MAXRATING")
os += root.get_objects("type", "RECOMMENDED")
os += root.get_objects("type", "EPM")

keys = Array.new
keys << "type"
keys << "name"
keys << "min"
keys << "typ"
keys << "max"
keys << "unit"
keys << "condition"
keys << "description"
keys << "customerTarget"
keys << "testTarget"
keys << "verificationTarget"

ret = ""
keys.each { |key|
  ret += "#{key};"
}
ret.sub!(/;$/, "\n")

os.each { |o|
  keys.each { |key|
    ret += "#{o.get_local_value(key)};"
  }
  ret.sub!(/;$/, "\n")
}

puts ret

