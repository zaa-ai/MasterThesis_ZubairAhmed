#!/usr/bin/ruby

require 'getoptlong'
require 'English'

class NilClass
  def length()
    0
  end
end

filenames             = Array.new()
syncff_instance_names = Array.new()
overwrite     = false
# is the check going to be disabled with a high replaced value or
# with commenting out (default)
timeDisable   = false
time          = "0"

# parse options
opts = GetoptLong.new(
  [ "--file"            , "-f", GetoptLong::REQUIRED_ARGUMENT ],
  [ "--overwrite"       , "-o", GetoptLong::NO_ARGUMENT       ],
  [ "--syncff"          , "-s", GetoptLong::REQUIRED_ARGUMENT ],
  [ "--timeDisable"     , "-t", GetoptLong::NO_ARGUMENT       ],
  [ "--help"            , "-h", GetoptLong::NO_ARGUMENT       ]
)

opts.each {|opt, arg|
  case opt
    when '--file'
      filenames << arg
    when '--overwrite'
      overwrite = true
    when '--syncff'
      syncff_instance_names << arg
    when '--timeDisable'
      timeDisable = true
    when '--help'
      puts "Patch SDF files - remove setup/hold checks on data pin of sync FF's"
      puts "Valid options"
      puts "-f    : input file to patch"
      puts "-o    : overwrite"
      puts "-s    : Sync FF instance name"
      puts "-h    : print this help message"
      exit 0
  end
}

# interpret all remaining args as file names
if (!ARGV.empty?)
  filenames.concat(ARGV)
end

if filenames.empty?
  puts "Please specify a file name!"
  exit
end
if syncff_instance_names.empty?
  puts "Please specify -s"
  exit
end

# ------------- main program ------------------

# prepare regular expression for instance names
inst_exp = Regexp.new(syncff_instance_names.join("|"))

filenames.each {|filename|

  read_file  = IO.readlines(filename)
  sync_found = false

  read_file.each {|line|
    if (sync_found == false)
      if (line =~ /\(INSTANCE (.*)/)
        if ($1 =~ inst_exp)
          sync_found = true
          #puts "sync_found=#{line}"
          next
        end
      end
    else
      if (line =~ /\(CELL/)
        sync_found = false
        next
      end
    end
    
    if (sync_found == true)
      if (line =~ /\((SETUP|HOLD|SETUPHOLD)\s*?\((posedge|negedge)\s*(D|I)/)
        #puts "replace=#{line}"
        if timeDisable == false
          line.insert(0,'//')
        else
          line.gsub!(/[\d\.-]+::/, "#{time}::")
          line.gsub!(/:[\d\.-]+:/, ":#{time}:")
          line.gsub!(/::[\d\.-]+/, "::#{time}")
        end
        #puts "now=    #{line}"
      end
    end
  }

  if overwrite
    File.open(filename, "w") { |file| file << read_file }
  else
    puts read_file
  end
}
