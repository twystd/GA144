class Erlang

  def initialize()
  end

  def to_s
    "erlang"
  end

  def codegen(opcode)
    function = opcode.opcode().to_s + "_test"
    vector   = "TEST_" + opcode.opcode().to_s.upcase
    before   = []
    after    = []
    padding  = "         " + " " * vector.length

    puts "Generating erlang eunit test: " + function

	opcode.spec().each do |operation|
  	  #puts "**     " + operation.to_s
  	  #puts "**:LHS " + operation.register
  	  #puts "**:RHS " + operation.expression
      case operation.register
        when 't'
          p = 123
          q = evaluate(p,operation.expression)
          x = "{t," + p.to_s + "}" 
          y = "{t," + q.to_s + "}" 
          before.push(x) 
          after.push (y) 
      end

    end

    puts
    puts "--- CODE ---"
    puts "-define(" + vector + ",[{?" + opcode.opcode().to_s.upcase + ","
    puts padding + "  [" + as_string(before) + "],"
    puts padding + "  [" + as_string(after)  + "]},"
    puts padding + "])."
    puts
    puts function + "() -> test_opcode(?" + vector + ")."
    puts
  end

  def as_string(array) 
    s = ""
    separator = ""
    array.each do |item|
      s += separator
      s += item.to_s
      separator = ","
    end
    s
  end

  def evaluate(v,expression) 
    v
  end
 
end
