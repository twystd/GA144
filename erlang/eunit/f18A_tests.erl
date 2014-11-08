-module(f18A_tests).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").

-define(GO,        [reset,nop,nop,nop,nop,nop,eof]).
-define(STEP,      [reset,nop,nop,nop,nop,nop,eof]).
-define(NOP,       [reset,nop]).
-define(NOP2,      [reset,nop,nop]).
-define(NOP3,      [reset,nop,nop,nop]).
-define(NOP4,      [reset,nop,nop,nop,nop]).
-define(NOP5,      [reset,nop,nop,nop,nop,nop]).
-define(FETCHP,    [reset,{fetchp,{t,16#1d5}}]).
-define(FETCHB,    [reset,{fetchp,{t,16#1d5}},{bstore,{b,16#1d5}},{fetchb,{t,678}}]).
-define(STOREB,    [reset,{fetchp,{t,16#1d5}},{bstore,{b,16#1d5}},{fetchp,{t,678}},nop,{storeb,{b,16#1d5},{t,678}}]).

-define(READ,      [reset,read,{read,678},eof]).
-define(WRITE,     [reset,{write,678},{write,ok},eof]).
-define(READ_STOP, [reset,nop,read,stop]).
-define(WRITE_STOP,[reset,nop,{write,123},stop]).
-define(READWRITE1,[reset,read,{read,135},nop,nop,nop,eof]).
-define(READWRITE2,[reset,nop,nop,{write,135},{write,ok},nop,eof]).
-define(WRITEREAD1,[reset,nop,nop,read,{read,135},nop,eof]).
-define(WRITEREAD2,[reset,{write,135},{write,ok},nop,nop,nop,eof]).

% EUNIT TESTS

go_test() ->
   M    = setup("-- GO TEST"),
   F18A = f18A:create(n001,n000,[nop,nop,nop,nop,nop]),

   f18A:breakpoint(F18A,2),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:go   (F18A,wait),
            M ! { n001,stopped }
         end),

   check(waitall([{n001,stopped}]),
         [ { ?GO,n001 }
         ]).

step_test() ->
   M    = setup("-- STEP TEST"),
   F18A = f18A:create(n001,n000,[nop,nop,nop,nop,nop]),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            M ! { n001,stopped }
         end),

   check(waitall([{n001,stopped}]),
         [ { ?STEP,n001 }
         ]).

nop_test() ->
   setup("-- NOP TEST"),
   F18A = f18A:create(n001,n000,[ 16#2d555 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?NOP,n001 }
         ]).

nop2_test() ->
   setup("-- NOP:2 TEST"),
   F18A = f18A:create(n001,n000,[ 16#2c955 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?NOP2,n001 }
         ]).

nop3_test() ->
   setup("-- NOP:3 TEST"),
   F18A = f18A:create(n001,n000,[ 16#2c9b5 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?NOP3,n001 }
         ]).

nop4_test() ->
   setup("-- NOP:4 TEST"),
   F18A = f18A:create(n001,n000,[ 16#2c9b2 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?NOP4,n001 }
         ]).

nop5_test() ->
   setup("-- NOP:5 TEST"),
   F18A = f18A:create(n001,n000,[ 16#2c9b2,16#2d555 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?NOP5,n001 }
         ]).

fetchp_test() ->
   setup("-- FETCH-P TEST"),
   F18A = f18A:create(n001,n000,[ 16#04000,16#001d5 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?FETCHP,n001 }
         ]).

fetchb_test() ->
   M    = setup("-- FETCH-B TEST"),
   F18A = f18A:create(n001,n000,[ 16#04b02,16#001d5 ]),

   f18A:reset(F18A),

   register(n000,spawn(fun() ->
                          n001 ! { n000,write,678 },
                          wait({n001,read,ok}),
                          M    ! { n000,stopped }
                       end)),

   spawn(fun() ->
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
   	      f18A:step (F18A,wait),
            M ! { n001,stopped }
	 end),

   check(waitall([{n000,stopped},{n001,stopped}]),
         [ { ?FETCHB,n001 }
         ]).

storeb_test() ->
   M    = setup("-- STORE-B TEST"),
   F18A = f18A:create(n001,n000,[ 16#04b12,16#001d5,16#002a6,16#089b2 ]),

   f18A:reset(F18A),

   register(n000,spawn(fun() ->
                          wait({ n001,write,678 }),
                          n001 ! { n000,read,ok },
                          M ! { n000,stopped }
                       end)),
   
   spawn(fun() ->
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:stop (F18A),
            M ! { n001,stopped }
	 end),

   check(waitall([{n000,stopped},{n001,stopped}]),
         [ { ?STOREB,n001 }
         ]).

read_go_test() ->
   M = setup("-- READ TEST/GO"),
   util:unregister(n000),

   F18A = f18A:create(n001,n000,[read]),

   f18A:reset(F18A),

   spawn(fun() ->
            f18A:go   (F18A,wait),
            M ! { n001,stopped }
         end),

   register(n000,spawn(fun() ->
                          n001 ! { n000,write,678 },
                          wait({n001,read,ok}),
                          M    ! { n000,stopped }
                       end)),
   
   check(waitall([{n000,stopped},{n001,stopped}]),
         [ { ?READ,n001 }
         ]).


read_step_test() ->
   M = setup("-- READ TEST/STEP"),
   util:unregister(n000),

   F18A = f18A:create(n001,n000,[read]),

   f18A:reset(F18A),

   spawn(fun() ->
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            M ! { n001,stopped }
         end),

   register(n000,spawn(fun() ->
                          n001 ! { n000,write,678 },
                          wait({n001,read,ok}),
                          M    ! { n000,stopped }
                       end)),
   
   check(waitall([{n000,stopped},{n001,stopped}]),
         [ { ?READ,n001 }
         ]).

write_go_test() ->
   M = setup("-- WRITE TEST/GO"),
   util:unregister(n000),
   util:unregister(n001),

   F18A = f18A:create(n001,n000,[{write,678}]),
   
   register(n000,spawn(fun() ->
                          wait({ n001,write,678 }),
                          n001 ! { n000,read,ok },
                          M ! { n000,stopped }
                       end)),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:go   (F18A,wait),
            M ! { n001,stopped }
         end),
         
   check(waitall([{n000,stopped},{n001,stopped}]),
         [ { ?WRITE,n001 }
         ]).

write_step_test() ->
   M = setup("-- WRITE TEST/STEP"),
   util:unregister(n000),
   util:unregister(n001),

   F18A = f18A:create(n001,n000,[{write,678}]),
   
   register(n000,spawn(fun() ->
                          wait({ n001,write,678 }),
                          n001 ! { n000,read,ok },
                          M ! { n000,stopped }
                       end)),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            M ! { n001,stopped }
         end),
         
   check(waitall([{n000,stopped},{n001,stopped}]),
         [ { ?WRITE,n001 }
         ]).

read_stop_go_test() ->
   setup("-- READ STOP TEST/GO"),
   F18A = f18A:create(n001,n000,[nop,read,nop,nop,nop]),
   f18A:reset(F18A),
   f18A:go   (F18A),
   f18A:stop (F18A,wait),

   check(waitall([]),
         [ { ?READ_STOP,n001 }
         ]).

read_stop_step_test() ->
   log:info(?TAG,"-- READ STOP TEST/STEP"),
   trace:stop (),
   trace:start(),
   F18A = f18A:create(n001,n000,[nop,read,nop,nop,nop]),
   f18A:reset(F18A),
   f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A), f18A:step (F18A),
   f18A:stop (F18A,wait),

   check(waitall([]),
         [ { ?READ_STOP,n001 }
         ]).

write_stop_go_test() ->
   setup("-- WRITE STOP TEST/GO"),
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
   f18A:go   (F18A), 
   f18A:stop (F18A,wait),

   check(waitall([]),
         [ { ?WRITE_STOP,n001 }
         ]).

write_stop_step_test() ->
   setup("-- WRITE STOP TEST/STEP"),

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

   check(waitall([]),
         [ { ?WRITE_STOP,n001 }
         ]).

readwrite_go_test() ->
   M = setup("-- READ-WRITE TEST/GO"),

   spawn(fun() ->
      F18A = f18A:create(n001,n002,[read,nop,nop,nop]),
      f18A:reset(F18A),
      f18A:go   (F18A,wait),
      M ! { n001,stopped }
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[nop,nop,{write,135},nop]),
      f18A:reset(F18A),
      f18A:go   (F18A,wait),
      M ! { n002,stopped }
      end),
      
   check(waitall([{n001,stopped},{n002,stopped}]),
         [ { ?READWRITE1,n001 },
           { ?READWRITE2,n002 }
         ]).

readwrite_step_test() ->
   M = setup("-- READ-WRITE TEST/STEP"),

   spawn(fun() ->
      F18A = f18A:create(n001,n002,[read,nop,nop,nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      M ! { n001,stopped }
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[nop,nop,{write,135},nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      M ! { n002,stopped }
      end),
      
   check(waitall([{n001,stopped},{n002,stopped}]),
         [ { ?READWRITE1,n001 },
           { ?READWRITE2,n002 }
         ]).

writeread_go_test() ->
   M = setup("-- WRITE-READ TEST/GO"),

   spawn(fun() ->
      F18A = f18A:create(n001,n002,[nop,nop,read,nop]),
      f18A:reset(F18A),
      f18A:go   (F18A,wait),
      M ! { n001,stopped } 
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[{write,135},nop,nop,nop]),
      f18A:reset(F18A),
      f18A:go   (F18A,wait),
      M ! { n002,stopped } 
      end),
      
   check(waitall([{n001,stopped},{n002,stopped}]),
        [ { ?WRITEREAD1,n001 },
          { ?WRITEREAD2,n002 }
        ]).

writeread_step_test() ->
   M = setup("-- WRITE-READ TEST/STEP"),

   spawn(fun() ->
      F18A = f18A:create(n001,n002,[nop,nop,read,nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      M ! { n001,stopped } 
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[{write,135},nop,nop,nop]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      M ! { n002,stopped } 
      end),
      
   check(waitall([{n001,stopped},{n002,stopped}]),
        [ { ?WRITEREAD1,n001 }, 
          { ?WRITEREAD2,n002 } 
        ]).

%% UTILILITY FUNCTIONS

setup(TestName) ->
   log:info(?TAG,TestName),
   trace:stop (),
   trace:start(),
   self().

check(_Trace,[]) ->
   ok;

check(Trace,[{Expected,ID}|T]) ->
   ?assertEqual(ok,verify:compare(Expected,trace:extract(Trace,ID),noprint)),
   check(Trace,T).

waitall([]) ->
   trace:stop();

waitall([H|T]) ->
   wait(H),
   waitall(T).

wait(X) ->
   receive 
      X -> ok
   end.

