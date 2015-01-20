#!/usr/bin/ruby -w

# Code generator to generate unit tests for opcode implementations from
# a TLA+ spec file
#
# Makes LOTS of assumptions about the structure of the TLA+ spec !! (because this
# is highly experimental, if you have to have a reason :-))

# ... parse command line

tla_file = nil
gen_type = nil
previous = ""

ARGV.each do|a| 
  if previous == "--tla"
     tla_file = a
  elsif previous == "--type"
     gen_type = a
  end

  previous = a
end 

# ... validate

unless tla_file != nil
  puts "Error: missing TLA+ file"
  puts ""
  puts "Usage: opcode.rb --tla <TLA file> --type [erlang]"
  puts ""
  exit
end

unless gen_type != nil
  puts "Error: missing code generation type"
  puts ""
  puts "Usage: opcode.rb --tla <TLA file> --type [erlang]"
  puts ""
  exit
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
  match = /"(.*?)"/m.match(token)
  if match != nil 
     opcodes << match[1]
  end
end

if opcodes.length < 2
  puts "Warning: TLA+ file OPCODES definition is empty"
  puts ""
  exit
end

puts "OPCODES:"
puts  opcodes
