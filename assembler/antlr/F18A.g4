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
    : label? (WS (origin|opcode|word|call|constant))+ (WS comment)?
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

comment
    : COMMENT
    ;

ORG
    : 'org'
    ;

OPCODE
    : 'ret' | ';'
    | '@p'
    | '@b'
    | '2*' | 'shl'
    | '2/' | 'shr'
    | '-'
    | '+'
    | 'and'
    | 'or'  | 'xor'
    | 'drop'
    | 'dup'
    | 'nop' | '.'
    | '!b'
    | '!'
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
