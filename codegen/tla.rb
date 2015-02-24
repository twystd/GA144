require "parslet"

class TLA < Parslet::Parser
  rule(:clause)      { str('opcode') >> equals >> opcode >> conjunction >> function }
  rule(:space)       { str(' ').repeat     }
  rule(:equals)      { space >> match('=') }
  rule(:opcode)      { space >> str('SHL') }
  rule(:function)    { space >> str('shl') }
  rule(:conjunction) { space >> str('/\\') }

  root :clause
end

