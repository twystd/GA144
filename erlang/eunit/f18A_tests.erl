-module(f18A_tests).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").

-define(READ,      [{f18X,{n001,reset}},{f18X,{n001,read}},     {f18X,{n001,read,{ok,678}}},{f18X,{n001,stop}}]).
-define(WRITE,     [{f18X,{n001,reset}},{f18X,{n001,write,678}},{f18X,{n001,write,ok}},     {f18X,{n001,stop}}]).
-define(READ_STEP, [{f18X,{n001,reset}},{f18X,{n001,nop}},{f18X,{n001,read}},     {f18X,{n001,stop}}]).
-define(WRITE_STEP,[{f18X,{n001,reset}},{f18X,{n001,nop}},{f18X,{n001,write,123}},{f18X,{n001,stop}}]).
-define(READWRITE1,[{f18X,{n001,reset}},{f18X,{n001,read}},{f18X,{n001,read,{ok,135}}},{f18X,{n001,nop}},      {f18X,{n001,nop}},     {f18X,{n001,nop}},{f18X,{n001,stop}}]).
-define(READWRITE2,[{f18X,{n002,reset}},{f18X,{n002,nop}}, {f18X,{n002,nop}},          {f18X,{n002,write,135}},{f18X,{n002,write,ok}},{f18X,{n002,nop}},{f18X,{n002,stop}}]).
-define(WRITEREAD1,[{f18X,{n001,reset}},{f18X,{n001,nop}},      {f18X,{n001,nop}},     {f18X,{n001,read}},{f18X,{n001,read,{ok,135}}},{f18X,{n001,nop}},{f18X,{n001,stop}}]).
-define(WRITEREAD2,[{f18X,{n002,reset}},{f18X,{n002,write,135}},{f18X,{n002,write,ok}},{f18X,{n002,nop}}, {f18X,{n002,nop}},          {f18X,{n002,nop}},{f18X,{n002,stop}}]).

% EUNIT TESTS

read_test() ->
   log:info   (?TAG,"-- READ TEST"),
   util:unregister(n000),
   util:unregister(n001),
   trace:stop (),
   trace:start(),

   M    = self(),
   F18A = f18X:create(n001,n000,[read]),

   spawn(fun() ->
            f18X:reset(F18A),
            f18X:step (F18A,wait),
            f18X:stop (F18A,wait),
            M ! { n001,stopped }
         end),

   register(n000,spawn(fun() ->
                          n001 ! { n000,write,678 },
                          wait({n001,read,ok}),
                          M    ! { n000,stopped }
                       end)),
   
   wait({n000,stopped}),
   wait({n001,stopped}),

   ?assertEqual(ok,verify:compare(?READ,trace:stop(),noprint)).

write_test() ->
   log:info   (?TAG,"-- WRITE TEST"),
   util:unregister(n000),
   util:unregister(n001),
   trace:stop (),
   trace:start(),

   M    = self(),
   F18A = f18X:create(n001,n000,[{write,678}]),
   
   register(n000,spawn(fun() ->
                          wait({ n001,write,678 }),
                          n001 ! { n000,read,ok },
                          M ! { n000,stopped }
                       end)),

   spawn(fun() ->
            f18X:reset(F18A),
            f18X:step (F18A,wait),
            f18X:stop (F18A,wait),
            M ! { n001,stopped }
         end),
         
   wait({n000,stopped}),
   wait({n001,stopped}),
   ?assertEqual(ok,verify:compare(?WRITE,trace:stop(),noprint)).

read_stop_test() ->
   log:info(?TAG,"-- READ STOP TEST"),
   trace:stop (),
   trace:start(),
   F18A = f18X:create(n001,n000,[nop,read,nop,nop,nop]),
   f18X:reset(F18A),
   f18X:step (F18A), f18X:step (F18A), f18X:step (F18A), f18X:step (F18A), f18X:step (F18A),
   f18X:stop (F18A,wait),
   ?assertEqual(ok,verify:compare(?READ_STEP,trace:stop(),noprint)).

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
                                 
   F18A = f18X:create(n001,n000,[nop,{write,123},nop,nop,nop]),
   f18X:reset(F18A),
   f18X:step (F18A), 
   f18X:step (F18A), 
   f18X:step (F18A), 
   f18X:step (F18A), 
   f18X:step (F18A),
   f18X:stop (F18A,wait),
   ?assertEqual(ok,verify:compare(?WRITE_STEP,trace:stop(),noprint)).

readwrite_test() ->
   log:info(?TAG,"-- READ/WRITE TEST"),
   trace:stop (),
   trace:start(),

   M = self(),

   spawn(fun() ->
      F18A = f18X:create(n001,n002,[read,nop,nop,nop]),
      f18X:reset(F18A),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:stop (F18A,wait),
      M ! { n001,stopped }
      end),

   spawn(fun() ->
      F18A = f18X:create(n002,n001,[nop,nop,{write,135},nop]),
      f18X:reset(F18A),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:stop (F18A,wait),
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
      F18A = f18X:create(n001,n002,[nop,nop,read,nop]),
      f18X:reset(F18A),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:stop (F18A,wait),
      M ! { n001,stopped } 
      end),

   spawn(fun() ->
      F18A = f18X:create(n002,n001,[{write,135},nop,nop,nop]),
      f18X:reset(F18A),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:step (F18A,wait),
      f18X:stop (F18A,wait),
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

