#!/usr/bin/ruby

# param 1      : package prefix
# param 2, etc : verilog filenames

require 'port_parser'
require 'port_to_vhdl'

@name = ARGV.shift

ret = "
-- --------------------------------------------------
-- auto generated component package ... do not edit !
-- --------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.utils_pkg.all;

package #{@name} is

"

ARGV.each do |arg|
	a = Port_parser.new(arg)

	a.parse_vlog()
	a.modules.each do |m|
		ret += m.to_vhdl_component()
	end
end

ret += "end #{@name};\n\n"

puts ret

