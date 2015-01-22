class OpCode

  def initialize(opcode,spec)
    @opcode = opcode
    @spec   = parse(spec)
  end

  def to_s
    @opcode.to_s + ": " + @spec
  end

  def parse(spec)
    spec 
  end

end
