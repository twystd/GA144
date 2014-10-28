calc2  0 org                                    # calc2: 3(x+5)

calc  5 . + dup 2* + ;
main  1 . dup calc !b main ;
init  left b!
      -1 main ;

a9 org init ;
