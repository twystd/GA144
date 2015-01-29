class OpCode

  def initialize(opcode,*spec)
    @opcode = opcode
    @spec   = parse(spec)
  end

  def opcode
    @opcode
  end

  def spec
    @spec
  end

  def to_s
    @opcode.to_s
  end

  def parse(spec)
    spec 
  end

  def parsex(spec)
    tokens = tokenize(spec)
    puts "TOKENS"
    puts tokens
    spec 
  end

  def tokenize(string)
    tokens = Array.new
    state  = :idle
    string.each_line do | line |
      index  = 0
      while index < string.length do
        ch     = string[index]
        index += 1

        case state
        when :idle
          case ch
          when " "
          when "\n"
          else
            puts "-- " + ch
          end
        end
      end
    end
    tokens
  end
end
