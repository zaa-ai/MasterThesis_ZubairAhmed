#!/usr/bin/env ruby

src_name = String.new(ARGV[0])
dst_name = String.new(ARGV[1])

$elements = Array.new

def explore(dir)
  Dir.glob("#{dir}/*").each { |f|
    $elements << String.new(f)
    if File.directory?($elements.last)
      explore($elements.last)
    end
  }
end

def derive_file(src_e, dst_e, src_name, dst_name, src_name_uc, dst_name_uc)

  src_fh = File.open("#{src_e}", "r")
  dst_fh = File.open("#{dst_e}", "w")

  if src_fh and dst_fh
    src_fh.each { |line|
      line.gsub!(/#{src_name}/, "#{dst_name}")
      line.gsub!(/#{src_name_uc}/, "#{dst_name_uc}")
      dst_fh.write(line)
    }
  end
end

src_name.sub!(/\/$/, "")
dst_name.sub!(/\/$/, "")

src_name_uc = String.new(src_name).upcase
dst_name_uc = String.new(dst_name).upcase

$elements << "#{src_name}"
explore(src_name)

$elements.each { |src_e|
  dst_e = String.new(src_e)
  dst_e.gsub!(/#{src_name}/, "#{dst_name}")
  dst_e.gsub!(/#{src_name_uc}/, "#{dst_name_uc}")

  puts "#{src_e} -> #{dst_e}"

  if File.directory?(src_e)
    Dir.mkdir(dst_e)
  else
    if (src_e =~ /\.htm$/) or (src_e =~ /\.o$/) or (src_e =~ /\.pack$/) \
    or (src_e =~ /\.FLM$/) or (src_e =~ /\.crf$/) or (src_e =~ /\.axf$/)  # these files will be skipped
      puts "  SKIPPED"
    else
      if (src_e =~ /\.exe$/)  # these files will be copied
        `cp -a "#{src_e}" "#{dst_e}"`
      else
        # derive destination file by adapting source file content ...
        derive_file(src_e, dst_e, src_name, dst_name, src_name_uc, dst_name_uc)
      end
    end
  end
}


