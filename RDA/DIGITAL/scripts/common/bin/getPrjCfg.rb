#!/usr/bin/env ruby

#############################################################################
# Description   : query project, module or tech config.xml file
#############################################################################

require 'getoptlong'
require 'rexml/document'
include REXML

@with_path      = false
@with_upcase    = false
@attribute      = nil
@tag_names      = false
@default        = nil
@local          = false
@quiet          = false
@verbose        = false
@root_path      = nil

@fileName       = Array.new

opts = GetoptLong.new(
  [ "--path"            , "-p", GetoptLong::NO_ARGUMENT       ],
  [ "--uc"              , "-u", GetoptLong::NO_ARGUMENT       ],
  [ "--attribute"       , "-a", GetoptLong::REQUIRED_ARGUMENT ],
  [ "--root-path"       , "-r", GetoptLong::REQUIRED_ARGUMENT ],
  [ "--file-name"       , "-f", GetoptLong::REQUIRED_ARGUMENT ],
  [ "--tag-names"       , "-t", GetoptLong::NO_ARGUMENT       ],
  [ "--default"         , "-d", GetoptLong::REQUIRED_ARGUMENT ],
  [ "--local"           , "-l", GetoptLong::NO_ARGUMENT       ],
  [ "--quiet"           , "-q", GetoptLong::NO_ARGUMENT       ],
  [ "--verbose"         , "-v", GetoptLong::NO_ARGUMENT       ],
  [ "--help"            , "-h", GetoptLong::NO_ARGUMENT       ]
)

opts.each {|opt, arg|
  case opt
    when '--path'
      @with_path = true
    when '--uc'
      @with_upcase = true
    when '--attribute'
      @attribute = arg
    when '--tag-names'
      @tag_names = true
    when '--default'
      @default = arg
    when '--local'
      @local = true
    when '--file-name'
      testvar = arg
      @fileName = Array(@fileName).push(:"#{arg}")
    when '--quiet'
      @quiet = true
    when '--verbose'
      @verbose = true
    when '--root-path'
      @root_path = arg
    when '--help'
      puts "Get values of project, module or tech config XML files"
      puts "-p        : add path to value"
      puts "-u        : upcase output"
      puts "-a name   : get attribute value"
      puts "-r path   : with search root path"
      puts "-t        : output all child tag names"
      puts "-d string : default return string, in case of no match"
      puts "-l        : only look into local XML file"
      puts "-q        : no error message if element was not found"
      puts "-v        : prints additional information to console"
      puts "-h        : print this help message"
      exit 0
  end
}

def get_hier_path(node, ancestors)
  if !node.attribute("path").nil?
    return node.attribute("path").value + "/";
  end
  ancestors.each { |a|
    if !a.attribute("path").nil?
      return a.attribute("path").value + "/";
    end
  }
  ""
end

def terminate
  if @quiet
    exit(0)
  else
    if !@default.nil?
      puts @default
      exit(1)
    end
    STDERR.puts "Neither project nor module nor tech config XML could be found in the file hierarchy !"
    STDERR.puts "Or the XPath query could not be resolved in the found files -> no results !"
    if @tag_names
      STDERR.puts "Query was: XML get tag names #{ARGV[0]} !"
    else
      STDERR.puts "Query was: #{ARGV[0]} !"
    end
    exit(1)
  end
end

if !@root_path.nil?
  Dir.chdir(@root_path)
end

work_dir = Dir.pwd
begin
  Dir.chdir(ENV['PROJECT_HOME'])
rescue
  if @verbose
    STDERR.puts "Warning: environment variable $PROJECT_HOME is missing!"
  end
  Dir.chdir("/");
end
project_home = Dir.pwd
Dir.chdir(work_dir)
result = ""

while (result == "")

  if @local
    xml_files = Dir["{project,module,tech,tests}_config.xml"]
  else
    xml_files = Array.new
    while xml_files.empty? and (work_dir != "/") and (work_dir.length >= project_home.length)
      if @fileName.empty?
        xml_files = Dir["{project,module,tech,tests}_config.xml"]
      else
        @fileName.each { |xml_file_name|
          # xml_files = Array(xml_files).push(:"#{Dir["#{Dir.pwd}/#{xml_file_name}"]}")
          # incFile = "#{Dir.pwd}/#{xml_file_name}"
          xml_files.push("#{Dir.pwd}/#{xml_file_name}")
        }
      end
      # puts "Result: #{xml_files.last}"
      if xml_files.empty?
        work_dir = File.dirname(work_dir)
        Dir.chdir(work_dir)
      end
    end
  end

  if @verbose
    xml_files.each { |xml_file_name|
      STDERR.puts "info: adding file #{xml_file_name}"
    }
  end

  if xml_files.empty?
    terminate()
  end

  while !xml_files.empty?
    xml_file = xml_files.shift
    f = File.open("#{xml_file}", "r")
    xml = REXML::Document.new(f)
    f.close
    ########################################
    # ason
    
    xml_path = "/tech/xi:include"    
    nodes = XPath.match(xml, xml_path)
    
    while !nodes.empty?
      incFile = "#{Dir.pwd}/#{nodes.shift.attribute("href")}"
      if @verbose
        STDERR.puts "info: adding include file: #{incFile}"
      end
      xml_files.push(incFile)
    end
    
    # !ason
    ########################################
    
    xml_path = "/config/#{ARGV[0]}"
    nodes = XPath.match(xml, xml_path)
    if nodes.length == 0
      xml_path = "/#{ARGV[0]}"
      nodes = XPath.match(xml, xml_path)
    end
    ancestors = XPath.match(xml, "#{xml_path}/ancestor::*")

    nodes.each { |node|
      ret = nil
      if !@attribute.nil?
        if !node.attribute(@attribute).nil?
          a = node.attribute(@attribute).value
          ret = `echo #{a}`
          ret.chomp!
        end
      else
        if @tag_names
          XPath.match(node, "#{xml_path}/*").each { |t|
            if !t.text.strip.empty?
              if ret.nil?
                ret = t.name
              else
                ret += " " + t.name
              end
            end
          }
        else
          if !node.text.nil?
            ret = node.text.strip
          end
        end
      end
      
      if @with_path
        path = get_hier_path(node, ancestors)
        path = `echo #{path}`

        # check for relative path value (not starting with "/")
        # and prepend XML file directory path ...
        if path !~ /^\//
          path = "#{work_dir}/#{path}"
        end

        path.chomp!
        if !ret.nil?
          ret = path + ret
        end
      end

      if @with_upcase and !ret.nil?
        ret = ret.upcase;
      end

      if !ret.nil?
        result += ret + "\n"
      end
    }
  end

  if @local
    break
  end

  Dir.chdir("..")
  work_dir = Dir.pwd
end

if result != ""
  puts result
else
  terminate()
end

