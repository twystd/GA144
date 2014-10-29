grammar F18A;

program
    : (comment)*
      EOL*
      (origin EOL)
      (line? EOL)+
    ;

origin
    : label? WS ORIGIN WS ORG (WS COMMENT)?
    ;

 line
    : comment
    | instruction
    ;

instruction
    : label? WS opcode (WS comment)?
    ;

label
    : name
    ;

opcode
    : OPCODE
    ;

name
    : NAME
    ;

comment
    : COMMENT
    ;

ORIGIN
    : [0-9]+
    ;

ORG
    : 'org'
    ;

OPCODE
    : 'nop'
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
