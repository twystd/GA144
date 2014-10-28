calc1  0 org                        # calc1: 2(x+3)

calc  3 . + dup + ;
main  1 . dup calc !b main ;
init  right b!
      -1 main ;

a9 org init ;
