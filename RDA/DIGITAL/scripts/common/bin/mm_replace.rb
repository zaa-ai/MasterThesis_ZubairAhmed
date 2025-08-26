#!/usr/bin/env ruby

# replaces multiple strings in one file
# input is a replace file:
# keyword1
# replace string1
# keyword2
# replace string1
# ...


usage = "Usage: mm_replace.rb <replacement file> <file to edit>"

if not ARGV.length == 2 then
  puts usage
elsif not File.exists? ARGV[0]
  puts usage
  puts "Non existent replacement file"
elsif not File.exists? ARGV[1]
  puts usage
  puts "Non existent input file"
else

  repl_file = File.readlines(ARGV[0])
  repl_file.each {|e|
    e.chomp!
    e.gsub!(/\//, "\\/")
    e.gsub!(/\[/, "\\[")
    e.gsub!(/\]/, "\\]")
  }
  i = 0
  while i < repl_file.length()
    if !repl_file[i].nil? && !repl_file[i+1].nil? && (repl_file[i].length() > 0)
      if !system("sed -i -e 's/#{repl_file[i]}/#{repl_file[i+1]}/' #{ARGV[1]}")
        puts "SED Error: #{repl_file[i]}/#{repl_file[i+1]}/"
      end
    end
    i+=2
  end
end
