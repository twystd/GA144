class Erlang

  def initialize()
  end

  def to_s
    "erlang"
  end

  def codegen(opcode)
    function = opcode.opcode().to_s + "_test"
    vector = "?TEST_" + opcode.opcode().to_s.upcase
    puts "Generating erlang eunit test: " + function
    puts
 
    puts "--- CODE ---"
# -define(TEST_NOP,[ {?NOP,
#                     [],
#                     []
#                    } ]).
    puts function + "() -> test_opcode(" + vector + ")."
    puts
  end

end
