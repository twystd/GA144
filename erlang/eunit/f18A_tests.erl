-module(f18A_tests).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(READ,      [{f18A,{1,reset}},{f18A,{1,read}},{f18A,{1,read,{ok,678}}},{f18A,{1,stop}}]).
-define(WRITE_STEP,[{f18A,{1,reset}},{f18A,{1,nop}},{f18A,{1,write,123}},{f18A,{1,stop}}]).

% EUNIT TESTS

read_test() ->
   trace:stop (),
   trace:start(),
   M    = self(),
   Ch   = channel:create(1),
   Prog = [ read ],
   F18A = f18A:create(1,Ch,Prog),

   spawn(fun() -> 
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:stop (F18A,wait),
            M ! { a,ok}
         end),

   spawn(fun() -> 
            channel:write(Ch,678),
            M ! { b,ok}
         end),

   ?assertEqual({ok,ok},wait(undefined,undefined)),
   ?assertEqual(ok,verify:compare(?READ,trace:stop(),noprint)).

write_test() ->
   M    = self(),
   Ch   = channel:create(1),
   Prog = [ {write,678} ],
   F18A = f18A:create(1,Ch,Prog),
 
   spawn(fun() -> 
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:stop (F18A,wait),
            M ! { a,ok } 
         end),

   spawn(fun() -> 
            M ! { b,channel:read (Ch) } 
         end),

   ?assertEqual({ok,{ok,678}},wait(undefined,undefined)).

write_step_test() ->
   trace:stop (),
   trace:start(),
   Ch   = channel:create(1),
   Prog = [ nop,{write,123},nop,nop,nop ],
   F18A = f18A:create(1,Ch,Prog),
   f18A:reset(F18A),
   f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A),
   f18A:stop (F18A,wait),
   ?assertEqual(ok,verify:compare(?WRITE_STEP,trace:stop(),noprint)).

wait({a,X},{b,Y}) ->
   {X,Y};

wait(X,Y) ->
   receive 
      { a,A } ->
         wait({a,A},Y);

      { b,B } ->
         wait(X,{b,B});

      _any ->
         wait(X,Y)
   end.

