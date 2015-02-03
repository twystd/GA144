class Erlang

  def initialize()
  end

  def to_s
    "erlang"
  end

  def codegen(opcode)
    puts "Generating erlang eunit test: " + function
 
    function = opcode.opcode().to_s + "_test"
    vector   = "TEST_" + opcode.opcode().to_s.upcase
    before   = []
    after    = []
    padding  = "         " + " " * vector.length

	opcode.spec().each do | operation |
  	  puts "  " + operation.to_s
    end

    puts
    puts "--- CODE ---"
    puts "-define(" + vector + ",[{?" + opcode.opcode().to_s.upcase + ","
    puts padding + "  [],"
    puts padding + "  []},"
    puts padding + "])."
    puts
    puts function + "() -> test_opcode(?" + vector + ")."
    puts
  end

end
