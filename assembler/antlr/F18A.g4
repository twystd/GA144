grammar F18A;

program
    : (comment)*
      EOL*
      (origin EOL)
      (line? EOL)+
    ;

origin
    : label? WS address WS ORG (WS COMMENT)?
    ;

 line
    : comment
    | instruction
    ;

instruction
    : label? (WS (opcode|word|call|constant))+ (WS comment)?
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
    | '+'
    | 'dup'
    | 'nop' | '.'
    | 'b!'
    | '!b'
    ;

WORD
    : 'right'
    ;

NUMBER
    : [\-]?[0-9]+
    ;

NAME
    : [a-zA-Z] [a-zA-Z0-9]*
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
