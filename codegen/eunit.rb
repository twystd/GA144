#!/usr/bin/ruby -w

load "opcode.rb"
load "operation.rb"

# Code generator to generate unit tests for opcode implementations from
# a TLA+ spec file
#
# Makes LOTS of assumptions about the structure of the TLA+ spec (and uses regex instead
# of an AST). Because this is a quick and dirty highly experimental version, if you have
# to have a reason :-))


# Utility method to extract the value of a 'named' command line argument
def arg(name,defval)
  previous = ""

  ARGV.each do|a| 
    if previous == name
      return a
    end
    previous = a
  end

  return defval
end

# Utility method to display a command line argument error and exit
def help(message)
  puts message
  puts ""
  puts "Usage: opcode.rb --tla <TLA file> --type [erlang]"
  puts ""
  exit
end

# ... parse command line

tla_file = arg("--tla",nil)
gen_type = arg("--type",nil)

unless tla_file != nil
  help("Error: missing TLA+ file")
end

unless gen_type != nil
  help("Error: missing code generation type")
end

puts "Generating " + gen_type + " opcode test vectors from " + tla_file
puts

# ... load TLA+ file

tla = IO.readlines(tla_file)

# ... get OPCODE list

match = /^\s*OPCODES\s*==\s*{(.*?)}/m.match(tla.join)

unless match != nil
  puts "Error: TLA+ file does not include definition OPCODES"
  puts ""
  exit
end

tokens = match[1].split(",")
opcodes = []

tokens.each do |token|
  match = /(\w+)/m.match(token)
  if match != nil 
     opcodes << match[1].to_sym
  end
end

if opcodes.length < 2
  puts "Warning: TLA+ file OPCODES definition is empty"
  puts ""
  exit
end

# ... get opcode definitions
#
# spec = Hash.new
# 
# opcodes.each do |opcode|
#   regex = Regexp.compile("#{opcode}\s*==(.*?)(^\s*[a-zA-Z0-9_]+\s*==)",Regexp::MULTILINE)
#   match = regex.match(tla.join)
# 
#   if (match) 
#     puts match[1]
#     spec[opcode] = OpCode.new(opcode,match[1])
#   else
#     puts "Warning: TLA+ file: missing definition for OPCODE #{opcode}"
#   end
# end
# 
# puts "---- SPEC"
# spec.each do | opcode,definition |
#   puts opcode.to_s + " [" + definition.to_s + "]"
#   end
# puts "----"

# --- NOP

unchanged = Operation.new("t","t")
nop = OpCode.new("nop",unchanged)

puts "---- NOP"
puts nop.to_s

nop.spec.each do | operation |
  puts "  " + operation.to_s
  end

puts "----"





