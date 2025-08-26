#!/usr/bin/env ruby

File.open(ARGV[0], 'r') { |f|
	while line = f.gets
	#line.sub!(/(^\s*\d*//.\d*\s*\d*//.\d*e//-\d*\s*)(.*\s)(.*)/,"\\1asic_shell/asic_inst/xdigtop/")
	line.sub!(/(^\s*\S*\s*\S*\s*)(\S*\s*)(.*)/,"\\1asic_shell/asic_inst/xdigtop/\\2asic_shell/asic_inst/xdigtop/\\3")
# output lines ...
	puts line
	end
}

