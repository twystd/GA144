#!/usr/bin/ruby -w

load "opcode.rb"
load "operation.rb"
load "erlang.rb"

# CONSTANTS

NEXT = "Next == \\/ /\\ opcode = SHL /\\ shl
                \\/ /\\ opcode = SHR /\\ shr
                \\/ /\\ opcode = NOT /\\ not
                \\/ /\\ opcode = NOP /\\ nop
                \\/ /\\ opcode  = UNKNOWN
                \/\\ UNCHANGED << opcode,CPU >>"

# MAIN

def main
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
  
  # ... get EDGE CASES
  
  match = /^\s*EDGE_CASES\s*==\s*{(.*?)}/m.match(tla.join)
  
  unless match != nil
    puts "Error: TLA+ file does not include definition EDGE_CASES"
    puts ""
    exit
  end
  
  tokens = match[1].split(",")
  edge_cases = []
  
  tokens.each do |token|
    match = /([+-]?[0-9]+)/m.match(token)
    if match != nil 
       edge_cases << match[1].to_i
    end
  end
  
  if edge_cases.length == 0
    puts "Warning: TLA+ file EDGE_CASES definition is empty"
    puts ""
    exit
  end
  
  # ... parse NEXT definition
  
  parseNext(NEXT)
  
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
  expression = Operation.new("T","T")
  nop = OpCode.new("nop",expression)
  
  # --- SHL
  expression = Operation.new("T","band(2*T,131071)")
  shl = OpCode.new("shl",expression)
  
  # --- SHR
  expression = Operation.new("T","T \\div 2")
  shr = OpCode.new("shr",expression)
  
  # --- NOT
  expression = Operation.new("T","-T - 1")
  inv = OpCode.new("not",expression)
  
  erlang = Erlang.new
  erlang.codegen(shl,edge_cases)
  erlang.codegen(shr,edge_cases)
  erlang.codegen(nop,edge_cases)
  erlang.codegen(inv,edge_cases)
  # erlang.print()
end

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

# Parses the TLA 'NEXT' definition
def parseNext(script)
  puts script
end

main
