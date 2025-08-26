#!/usr/bin/env ruby

if (ARGV.size != 2)
  puts "param0: input ELF disassemble file"
  puts "param1: output header file"
  exit 1
end

class Func_desc

  attr_accessor :func, :addr

  def initialize(func, addr)
    @func = func
    @addr = addr
  end

  def <=>(other)
    @addr.hex <=> other.addr.hex
  end
end

h_name = String.new(ARGV[1])

h_name.gsub!(/.*\//, "")
h_name.gsub!(/\.h/, "")

functions = Array.new

File.new(ARGV[0]).each { |line|
  line.strip!
  if line =~ /^([\da-fA-F]+)\s+<([\w_]+)>:/
    addr = $1.strip
    func = $2.strip
    if func =~ /^[a-zA-Z]/
      functions << Func_desc.new(func, addr)
    end
  end
}

functions.sort!

ret = ""
ret += "#ifndef #{h_name.upcase}_H\n"
ret += "#define #{h_name.upcase}_H\n"
ret += "\n"

len = 0
functions.each {|f|
  if len < f.func.length
    len = f.func.length
  end
}
functions.each {|f|
  ret += "#define AADDR_#{h_name.upcase}_" + "#{f.func.upcase}".ljust(len) + " (0x#{f.addr})\n"
}

ret += "\n"
ret += "#endif  // #{h_name.upcase}_H\n"
ret += "\n"

File.open(ARGV[1], "w") { |f|
  f << ret
}

