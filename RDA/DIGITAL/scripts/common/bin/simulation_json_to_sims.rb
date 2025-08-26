#!/usr/bin/env ruby

require 'json_parser'

if ARGV.length < 1
  puts "Usage: simulation_json_to_sims.rb <simulation-json-file>"
  exit
end

root = Json_parser.new(ARGV[0]).root

os = Array.new
os += root.get_objects("type", "STASK")

keys = Array.new
keys << "name"
keys << "taskState"
keys << "customerTarget"

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

