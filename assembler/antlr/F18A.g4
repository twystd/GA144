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
    : label? (WS (opcode|word|constant))+ (WS comment)?
    ;

label
    : name
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
name
    : NAME
    ;

comment
    : COMMENT
    ;

ORG
    : 'org'
    ;

OPCODE
    : 'nop' | '.'
    | '@p'
    | '@b'
    | 'b!'
    | '!b'
    ;

WORD
    : 'right'
    ;

NUMBER
    : [0-9]+
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
