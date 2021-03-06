grammar F18A;

program
    : (comment)*
      EOL*
      (label? WS origin EOL)
      (line? EOL)+
    ;

origin
    : address WS ORG (WS COMMENT)?
    ;

 line
    : comment
    | instruction
    ;

instruction
    : label? (WS (origin|opcode|word|call|next|jz|jp|constant))+ (WS comment)?
    ;

label
    : NAME
    ;

address
    : NUMBER
    ;

opcode
    : OPCODE
    ;

word
    : WORD
    ;

constant
    : NUMBER
    ;

call
    : NAME
    ;

next
    : 'next' WS NAME
    ;

jz
    : 'if' WS NAME
    ;

jp
    : '-if' WS NAME
    ;

comment
    : COMMENT
    ;

ORG
    : 'org'
    ;

OPCODE
    : 'ret' | ';'
    | 'ex'
    | 'unext'
    | '@p'
    | '@+'
    | '@b'
    | '@'
    | '!p'
    | '!+'
    | '!b'
    | '!'
    | '+*' | 'multiply'
    | '2*' | 'shl'
    | '2/' | 'shr'
    | '-'
    | '+'
    | 'and'
    | 'or'  | 'xor'
    | 'drop'
    | 'dup'
    | 'pop'
    | 'over'
    | 'a'
    | 'nop' | '.'
    | 'push'
    | 'b!'
    | 'a!'
    ;

WORD
    : 'right'
    | 'left'
    | 'down'
    ;

NUMBER
    : ([\-]?[0-9]+)|([a-fA-F0-9]+ 'H')
    ;

NAME
    : [a-zA-Z] [a-zA-Z0-9!@]*
    ;

COMMENT
    : '#' ~[\r\n]*
    ;

EOL
    : '\r'? '\n'
    ;
     
WS
    : [ ]+
    ;
