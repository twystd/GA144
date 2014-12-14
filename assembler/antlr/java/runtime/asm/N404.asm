calc1 0 org

calc   3 . + dup + ;
main   1 . + dup calc !b main ;
init   right b!
       -1 main ;

       a9H org init ;