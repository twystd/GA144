-module(user_default).

-compile(export_all).

s() ->
   sync:start().

x() ->
   f18A:test().

xx() ->
   f18A_tests:nop5_test().    

r() ->
   make:all([load]).
