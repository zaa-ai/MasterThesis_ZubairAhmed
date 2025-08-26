#!/usr/bin/env ruby
require 'mux_parser'
require 'mux_to_vlog'

#param0: ODS or ODT file
#param1: table name
#param2: output file
#param3: multiplexer entity name

system("unzip -o #{ARGV[0]} content.xml")


mp = Mux_parser.new("content.xml")
mp.read_mux_table(ARGV[1])
#puts mp.to_s
#mp.mux_list = mp.mux_list.process_input_muxes()

File.open(ARGV[2], "w") { |file| file << mp.mux_list.to_vlog_pure_iomux(ARGV[3])}


system("rm -f content.xml")
