accumulator 0 org                        # accumulator: calc1 + calc2

rsinit   down a! ;
rs!      ! ;
c1@      right b! @b ;
c2@      left  b! @b ;
main     c1@ + c2@ + rs!
         main ;

init rsinit 0 main ;

a9 org init ;
