-module(user_default).

-compile(export_all).

s() ->
   sync:start().

x() ->
   f18A:test().

xx() ->
   ga144:hccforth_test().    

r() ->
   make:all([load]).
