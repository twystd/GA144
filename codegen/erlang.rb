class Erlang

  MAXLENGTH = 24

  def initialize()
    @defines = []
    @tests   = []
  end

  def to_s
    "erlang"
  end
  
  # Prints the eunit tests to the console

  def print 
    puts
    puts "** ERLANG **"
    puts

    @defines.each do |define|
      puts define
      puts
    end
   
   @tests.each do |test|
     puts test
   end
 
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
          when 'T'
            p = edge_case
            q = evaluate(p,operation.expression)
            x = "{t," + to_hex(p) + "}" 
            y = "{t," + to_hex(q) + "}" 
            before.push(x) 
            after.push (y) 
        end
      end

      vectors.push(TestVector.new(opcode.opcode().to_s.upcase,before,after))
    end

    # ... generate eunit test

    define  = ""
    test    = "TEST_" + opcode.opcode().to_s.upcase
    prefix  = "-define(" + test + ",["
    suffix  = ""
    padding = "         " + " " * test.length

    vectors.each do |vector|
      before = to_string(vector.before())
      after  = to_string(vector.after())

      if before.length < MAXLENGTH && after.length < MAXLENGTH 
        define += suffix
        define += prefix  + "{?" + vector.opcode() + ","
        define += "[" + before + "],"
        define += "[" + after  + "]}"
      else 
        define += suffix
        define += prefix  + "{?" + vector.opcode() + ",\n"
        define += padding + "  [" + before + "],\n"
        define += padding + "  [" + after  + "]}"
      end 

      prefix = padding + " "
      suffix = ",\n"
    end

    define += "\n" + padding + "])."

    # ... add to definitions

    @defines.push(define)
    @tests.push(function + "() -> test_opcode(?" + test + ").")

    # ... write to f18A_test.hrl

    # puts
    # puts "--- CODE ---"
    # puts
    # puts string
    # puts
    # puts function + "() -> test_opcode(?" + test + ")."
    # puts
  end

  def to_string(array) 
    s = ""
    separator = ""
    array.each do |item|
      s += separator
      s += item.to_s
      separator = ","
    end
    s
  end

  def to_hex(value) 
    if value < 0
      "16#%05x" % (0x40000 + value)
    else
      "16#%05x" % value
    end
  end

  def evaluate(v,expression) 
    eval(expression.gsub("T",v.to_s)
                   .gsub("\\div","/"))
  end

  def band(a,b)
    if (a < 0)
      -bandx(-a,b)
    else
      bandx(a,b)
    end 
  end

  def bandx(a,b)
     if (a > b)
       a-(b+1)
     else
       a
     end
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
