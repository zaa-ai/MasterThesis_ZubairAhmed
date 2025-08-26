#!/usr/bin/env ruby

require 'device_config'

dc = DeviceConfig.new()
dc.parse()

puts ""
dc.config.keys.sort.each { |t|
  value = dc.config[t]

  if value == "false"
    value = "0"
  end
  if value == "true"
    value = "1"
  end

  puts "#{t.upcase.ljust(dc.max_length)} = #{value}"
}
puts ""

