#!/usr/bin/env ruby

def sv_to_c_type(sv_type = "", sign = "")
  c_type = ""

  if sign == "unsigned"
    c_type += "unsigned "
  end

  if sv_type == "longint"
    c_type += "long long"
  end
  if sv_type == "int"
    c_type += "long"
  end
  if sv_type == "shortint"
    c_type += "short"
  end
  if sv_type == "byte"
    c_type += "char"
  end

  if c_type.empty?
    c_type = "void"
  end
  c_type
end

class TaskParam

  #attr_accessor :dir, :c_type, :sign, :name

  def initialize(dir, sv_type, sv_sign, name)
    @dir    = dir                             # parameter direction: input / output
    @c_type = sv_to_c_type(sv_type, sv_sign)  # parameter type
    @name   = name                            # parameter name
  end

  def to_s
    ret = @c_type + " "

    if @dir == "output"
      ret += "*"
    end
    ret += @name
    ret
  end
end

class Task

  attr_accessor :dir, :c_type, :name, :params

  def initialize(dir, name)
    @dir    = dir             # task or function direction: import / export
    @c_type = sv_to_c_type()  #         function return type
    @name   = name            # task or function name
    @params = Array.new       # task of function parameters
  end

  def set_type(sv_type)
    @c_type = sv_to_c_type(sv_type)
  end

  def to_s
    ret = ""
    ret += "extern #{@c_type} #{@name}("
    if params.length > 0
      params.each_index { |n|
        ret += params[n].to_s
        if n < params.length-1
          ret += ", "
        end
      }
    else
      ret += "void"
    end
    ret += ");\n"
  end
end

class Declarations

  attr_accessor :name, :tasks

  def initialize(name)
    fname = String.new(name)
    @name  = fname.upcase     # C header name
    @tasks = Array.new        # tasks and functions

    @name.gsub!(/\./, "_")    # . -> _
    @name.gsub!(/.*\//, "")   # remove path
  end

  def task_by_name(name)
    @tasks.each { |t|
      if t.name == name
        return t
      end
    }
    nil
  end

  def to_s
    ret = ""
    ret += "#ifndef #{@name}\n"
    ret += "#define #{@name}\n"
    ret += "\n"
    ret += "#ifdef __cplusplus\n"
    ret += "extern \"C\" {\n"
    ret += "#endif\n"
    ret += "\n"
    ret += "// HDL -> C\n"
    @tasks.each { |t|
      if t.dir == "export"
        ret += t.to_s
      end
    }
    ret += "\n"
    ret += "// C -> HDL\n"
    @tasks.each { |t|
      if t.dir == "import"
        ret += t.to_s
      end
    }
    ret += "\n"
    ret += "#ifdef __cplusplus\n"
    ret += "}\n"
    ret += "#endif\n"
    ret += "\n"
    ret += "#endif // #{@name}\n"
    ret
  end
end

#==========================================================================

declarations = Declarations.new(ARGV[1])
task = nil

File.new(ARGV[0]).each { |line|
  line.gsub!(/\(\)/, "")
  line.gsub!(/task automatic /, "task ")
  line.gsub!(/function automatic /, "function ")

  if line =~ /^\s*(export)\s+"DPI.*"\s+task\s+(\w+)\s*;/
    declarations.tasks << Task.new($1, $2)
  end
  if line =~ /^\s*(import)\s+"DPI.*"\s+task\s+(\w+)\s*;/
    declarations.tasks << Task.new($1, $2)
  end
  if line =~ /^\s*(import)\s+"DPI.*"\s+context\s+task\s+(\w+)\s*;/
    declarations.tasks << Task.new($1, $2)
  end

  if line =~ /^\s*(export)\s+"DPI.*"\s+function\s+(\w+)\s*;/
    declarations.tasks << Task.new($1, $2)
  end
  if line =~ /^\s*(import)\s+"DPI.*"\s+function\s+(\w+)\s+(\w+)\s*[\(;]/
    task = Task.new($1, $3)
    task.set_type($2)
    declarations.tasks << task
  end

  if line =~ /^\s*task\s+(\w+)\s*[\(;]/
    task = declarations.task_by_name($1)
    next
  end
  if line =~ /^\s*function\s+(\w+)\s+(\w+)\s*[\(;]/
    task = declarations.task_by_name($2)
    if !task.nil?
      task.set_type($1)
    end
    next
  end

  if line =~ /^\s*\)\s*;/
    task = nil
    next
  end

  if !task.nil?
    if line =~ /^\s*(input)\s+(\w+)\s+(unsigned)\s+(\w+)\s*,*/
      task.params << TaskParam.new($1, $2, $3, $4)
    else
      if line =~ /^\s*(input)\s+(\w+)\s+(\w+)\s*,*/
        task.params << TaskParam.new($1, $2, "signed", $3)
      end
    end
    if line =~ /^\s*(output)\s+(\w+)\s+(unsigned)\s+(\w+)\s*,*/
      task.params << TaskParam.new($1, $2, $3, $4)
    else
      if line =~ /^\s*(output)\s+(\w+)\s+(\w+)\s*,*/
        task.params << TaskParam.new($1, $2, "signed", $3)
      end
    end
  end
}

file = File.open(ARGV[1], "w")
file.puts declarations.to_s
file.close

