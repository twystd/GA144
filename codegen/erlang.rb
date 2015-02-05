class Erlang

  MAXLENGTH = 24

  def initialize()
  end

  def to_s
    "erlang"
  end

  # Code generation function for eunit tests

  def codegen(opcode,edge_cases)
    function = opcode.opcode().to_s + "_test"

    puts "Generating erlang eunit test: " + function

    # ... build test vectors

    vectors = []

    edge_cases.each do |edge_case|
      before = []
      after = []

	  opcode.spec().each do |operation|
        case operation.register
          when 't'
            p = edge_case
            q = evaluate(p,operation.expression)
            x = "{t," + p.to_s + "}" 
            y = "{t," + q.to_s + "}" 
            before.push(x) 
            after.push (y) 
        end
      end

      vectors.push(TestVector.new(opcode.opcode().to_s.upcase,before,after))
    end

    # ... generate eunit test

    string  = ""
    test    = "TEST_" + opcode.opcode().to_s.upcase
    prefix  = "-define(" + test + ",["
    suffix  = ""
    padding = "         " + " " * test.length

    vectors.each do |vector|
      before = as_string(vector.before())
      after  = as_string(vector.after())

      if before.length < MAXLENGTH && after.length < MAXLENGTH 
        string += suffix
        string += prefix  + "{?" + vector.opcode() + ","
        string += "[" + before + "],"
        string += "[" + after  + "]}"
      else 
        string += suffix
        string += prefix  + "{?" + vector.opcode() + ",\n"
        string += padding + "  [" + before + "],\n"
        string += padding + "  [" + after  + "]}"
      end 

      prefix = padding + " "
      suffix = ",\n"
    end

    string += "\n" + padding + "])."

    # ... write to f18A.hrl

    puts
    puts "--- CODE ---"
    puts
    puts string
    puts
    puts function + "() -> test_opcode(?" + test + ")."
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
 
  # Nested class to store generated test vectors

  class TestVector
    def initialize(opcode,before,after)
      @opcode = opcode
      @before = before
      @after = after
    end

    def opcode
      return @opcode
    end

    def before
      return @before
    end

    def after
      return @after
    end
  end

end
