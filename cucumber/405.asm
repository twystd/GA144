accumulator 0 org

rsinit   down a! ;
rs!      ! ;
c1@      right b! @b ;
c2@      left  b! @b ;
main     c1@ + c2@ + rs!
         0 main ;                 # NOTE: error in tutorial ??

init     rsinit 0 main ;

         a9H org init ;
