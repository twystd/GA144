class Operation
  def initialize(lhs,rhs)
    @register = lhs
    @expression = rhs
  end

  def register
    @register
  end

  def expression
    @expression
  end

  def to_s 
    @register.to_s + "' = " + @expression.to_s
  end 
end
