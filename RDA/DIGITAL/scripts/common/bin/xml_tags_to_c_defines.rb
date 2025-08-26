#!/usr/bin/env ruby

require 'device_config'

dc = DeviceConfig.new()
dc.parse()

puts "#ifndef DEVICE_CONFIG_H"
puts "#define DEVICE_CONFIG_H"
puts ""
dc.config.keys.sort.each { |t|
  value = dc.config[t]
  pre = "  "

  if value == "false"
    pre = "//"
    value = ""
  end
  if value == "true"
    pre = "  "
    value = ""
  end

  puts "#{pre}#define #{t.upcase.ljust(dc.max_length)}  #{value}"

  if /CORTEX_M/.match(value)
    puts "#{pre}#define #{value}"
  end
}
puts ""
puts "#endif  // DEVICE_CONFIG_H"

