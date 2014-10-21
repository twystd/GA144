-module(f18A_tests).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").

-define(READ,      [{f18A,{1,reset}},{f18A,{1,read}},     {f18A,{1,read,{ok,678}}},{f18A,{1,stop}}]).
-define(WRITE,     [{f18A,{1,reset}},{f18A,{1,write,678}},{f18A,{1,write,ok}},     {f18A,{1,stop}}]).
-define(READ_STEP, [{f18A,{1,reset}},{f18A,{1,nop}},{f18A,{1,read}},     {f18A,{1,stop}}]).
-define(WRITE_STEP,[{f18A,{1,reset}},{f18A,{1,nop}},{f18A,{1,write,123}},{f18A,{1,stop}}]).
-define(READWRITE, [{f18A,{1,reset}},{f18A,{1,read}},     {f18A,{1,read,{ok,678}}},{f18A,{1,stop}}]).

% EUNIT TESTS

read_test() ->
   log:info(?TAG,"-- READ TEST"),
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
   log:info(?TAG,"-- WRITE TEST"),
   trace:stop (),
   trace:start(),
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

   ?assertEqual({ok,{ok,678}},wait(undefined,undefined)),
   ?assertEqual(ok,verify:compare(?WRITE,trace:stop(),noprint)).

read_step_test() ->
   log:info(?TAG,"-- READ STEP TEST"),
   trace:stop (),
   trace:start(),
   Ch   = channel:create(1),
   Prog = [ nop,read,nop,nop,nop ],
   F18A = f18A:create(1,Ch,Prog),
   f18A:reset(F18A),
   f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A),
   f18A:stop (F18A,wait),
   ?assertEqual(ok,verify:compare(?READ_STEP,trace:stop(),noprint)).

write_step_test() ->
   log:info(?TAG,"-- WRITE STEP TEST"),
   trace:stop (),
   trace:start(),
   Ch   = channel:create(1),
   Prog = [ nop,{write,123},nop,nop,nop ],
   F18A = f18A:create(1,Ch,Prog),
   f18A:reset(F18A),
   f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A),
   f18A:stop (F18A,wait),
   ?assertEqual(ok,verify:compare(?WRITE_STEP,trace:stop(),noprint)).

readwrite_test() ->
   log:info(?TAG,"-- READ/WRITE TEST"),
   trace:stop (),
   trace:start(),

   Ch   = channel:create(1),
   Prog1 = [ read,nop,nop,        nop ],
   Prog2 = [ nop, nop,{write,135},nop ],
   F18A1 = f18A:create(1,Ch,Prog1),
   F18A2 = f18A:create(2,Ch,Prog2),

   f18A:reset(F18A1), f18A:reset(F18A2),
   f18A:step (F18A1), f18A:step (F18A2),
   f18A:step (F18A1), f18A:step (F18A2),
   f18A:step (F18A1), f18A:step (F18A2),
   f18A:step (F18A1), f18A:step (F18A2),
   f18A:stop (F18A1,wait), f18A:stop (F18A2,wait),

   Trace = trace:stop(),
   ?assertEqual(ok,verify:compare(?READWRITE,Trace,print)).

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

