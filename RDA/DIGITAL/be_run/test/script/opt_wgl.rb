#!/usr/bin/env ruby

## Remove TMODE stuff from wgl
# creating the new file
new_filename = ARGV[0] + '_changed'
nf = File.new(new_filename, 'a')

File.open(ARGV[0], 'r') { |f|
  while line = f.gets

    # remove TMODE signal stuff ...
    if line =~ /TMODE.*;/
      next
    end
    line.sub!(/"TMODE", /, "")

    # remove TMODE column ...
    if line =~ /(\s*vector\(.* \[ ). (.*\].*\n)/
      line = $1 + $2
    end

    # output lines ...
    #puts line
    nf.write(line);
  end

 }
nf.close();

