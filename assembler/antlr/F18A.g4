grammar F18A;

prog
    : (line? EOL)+
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
      { System.out.println("COMMENT: " + $COMMENT.text);
      }
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
