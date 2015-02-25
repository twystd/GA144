require "parslet"

class TLA < Parslet::Parser
  rule(:expression)  { clause | (disjunction >> clause).repeat }
  rule(:clause)      { space >> str('opcode') >> equals >> opcode >> conjunction >> function }
  rule(:equals)      { space >> match('=') }
  rule(:opcode)      { space >> (str('SHL') | str('SHR') | str('NOT') | str('NOP')) }
  rule(:function)    { space >> (str('shl') | str('shr') | str('not') | str('nop')) }
  rule(:conjunction) { space >> str('/\\') }
  rule(:disjunction) { space >> str('\\/') }
  rule(:space)       { str(' ').repeat     }

  root :expression
end

