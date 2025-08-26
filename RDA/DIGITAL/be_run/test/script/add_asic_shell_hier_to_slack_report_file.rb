#!/usr/bin/env ruby

File.open(ARGV[0], 'r') { |f|
	while line = f.gets
#	line.sub!(/(^\s*\S*\s*\S*\s*)(\S*\s*)(.*)/,"\\1asic_shell/asic_inst/xdigtop/\\2asic_shell/asic_inst/xdigtop/\\3")
	line.sub!(/(^\s(\s*((\d+[.]\d+)|[*])){4}\s)(.*)/,"\\1asic_shell/asic_inst/xdigtop/\\5")
# output lines ...
	puts line
	end
}

