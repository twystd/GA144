-module(f18A_tests).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").

-define(READ,      [reset,read,{read,678},stop]).
-define(WRITE,     [reset,{write,678},{write,ok},stop]).
-define(READ_STEP, [reset,nop,read,stop]).
-define(WRITE_STEP,[reset,nop,{write,123},stop]).
-define(READWRITE1,[reset,read,{read,135},nop,nop,nop,stop]).
-define(READWRITE2,[reset,nop,nop,{write,135},{write,ok},nop,stop]).
-define(WRITEREAD1,[reset,nop,nop,read,{read,135},nop,stop]).
-define(WRITEREAD2,[reset,{write,135},{write,ok},nop,nop,nop,stop]).

% EUNIT TESTS

read_test() ->
   log:info   (?TAG,"-- READ TEST"),
   util:unregister(n000),
   util:unregister(n001),
   trace:stop (),
   trace:start(),

   M    = self(),
   F18A = f18A:create(n001,n000,[read]),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:stop (F18A,wait),
            M ! { n001,stopped }
         end),

   register(n000,spawn(fun() ->
                          n001 ! { n000,write,678 },
                          wait({n001,read,ok}),
                          M    ! { n000,stopped }
                       end)),
   
   wait({n000,stopped}),
   wait({n001,stopped}),

   Trace = trace:stop(),

   ?assertEqual(ok,verify:compare(?READ,trace:extract(Trace,n001),noprint)).

write_test() ->
   log:info   (?TAG,"-- WRITE TEST"),
   util:unregister(n000),
   util:unregister(n001),
   trace:stop (),
   trace:start(),

   M    = self(),
   F18A = f18A:create(n001,n000,[{write,678}]),
   
   register(n000,spawn(fun() ->
                          wait({ n001,write,678 }),
                          n001 ! { n000,read,ok },
                          M ! { n000,stopped }
                       end)),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:stop (F18A,wait),
            M ! { n001,stopped }
         end),
         
   wait({n000,stopped}),
   wait({n001,stopped}),

   Trace = trace:stop(),

   ?assertEqual(ok,verify:compare(?WRITE,trace:extract(Trace,n001),noprint)).

read_stop_test() ->
   log:info(?TAG,"-- READ STOP TEST"),
   trace:stop (),
   trace:start(),
   F18A = f18A:create(n001,n000,[nop,read,nop,nop,nop]),
   f18A:reset(F18A),
   f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A),
   f18A:stop (F18A,wait),

   Trace = trace:stop(),

   ?assertEqual(ok,verify:compare(?READ_STEP,trace:extract(Trace,n001),noprint)).

write_stop_test() ->
   log:info(?TAG,"-- WRITE STOP TEST"),
   trace:stop (),
   trace:start(),
   register(n000,spawn(fun() -> 
                           receive
                              _ -> ok
                           end,
                        util:unregister(n000)
                        end)),
                                 
   F18A = f18A:create(n001,n000,[nop,{write,123},nop,nop,nop]),
   f18A:reset(F18A),
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A),
   f18A:stop (F18A,wait),

   Trace = trace:stop(),

   ?assertEqual(ok,verify:compare(?WRITE_STEP,trace:extract(Trace,n001),noprint)).

readwrite_test() ->
   log:info(?TAG,"-- READ/WRITE TEST"),
   trace:stop (),
   trace:start(),

   M = self(),

   spawn(fun() ->
      F18A = f18A:create(n001,n002,[read,nop,nop,nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:stop (F18A,wait),
      M ! { n001,stopped }
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[nop,nop,{write,135},nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:stop (F18A,wait),
      M ! { n002,stopped }
      end),
      
   wait({n001,stopped}),
   wait({n002,stopped}),

   Trace = trace:stop(),

   ?assertEqual(ok,verify:compare(?READWRITE1,trace:extract(Trace,n001),noprint)),
   ?assertEqual(ok,verify:compare(?READWRITE2,trace:extract(Trace,n002),noprint)).

writeread_test() ->
   log:info(?TAG,"-- WRITE/READ TEST"),
   trace:stop (),
   trace:start(),

   M  = self(),

   spawn(fun() ->
      F18A = f18A:create(n001,n002,[nop,nop,read,nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:stop (F18A,wait),
      M ! { n001,stopped } 
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[{write,135},nop,nop,nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:stop (F18A,wait),
      M ! { n002,stopped } 
      end),
      
   wait({n001,stopped}),
   wait({n002,stopped}),

   Trace = trace:stop(),

   ?assertEqual(ok,verify:compare(?WRITEREAD1,trace:extract(Trace,n001),noprint)),
   ?assertEqual(ok,verify:compare(?WRITEREAD2,trace:extract(Trace,n002),noprint)).

wait(X) ->
   receive 
      X -> ok
   end.

