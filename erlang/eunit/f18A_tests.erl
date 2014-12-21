-module(f18A_tests).

% INCLUDES

-include_lib("eunit/include/eunit.hrl").

% DEFINES

-define(TAG,"F18A").
-define(HCCFORTH,"../cucumber/hccforth.feature").

-define(CALL0,       {call,{p,0}}).
-define(FETCHP_RIGHT,{fetchp,{t,16#1d5}}).
-define(FETCHP_678,  {fetchp,{t,678}}).
-define(FETCHB_678,  {fetchb,{t,678}}).
-define(BSTORE_RIGHT,{bstore,{b,16#1d5}}).
-define(STOREB_RIGHT,{storeb,{b,16#1d5},{t,16#1d5}}).

-define(GO,        [reset,?CALL0,nop,nop,nop,nop,nop,nop,nop,nop,nop,nop,nop,nop,eof]).
-define(STEP,      [reset,{call,{p,0}},nop,nop,nop,nop,nop,nop,nop,nop,nop,nop]).
-define(BREAKPOINT,[reset,{call,{p,0}},nop,nop,nop,nop,nop,nop,nop,nop,nop,nop,nop,nop]).
-define(NOP,       [reset,{call,{p,0}},nop]).
-define(NOP2,      [reset,{call,{p,0}},nop,nop]).
-define(NOP3,      [reset,{call,{p,0}},nop,nop,nop]).
-define(NOP4,      [reset,{call,{p,0}},nop,nop,nop,nop]).
-define(NOP5,      [reset,{call,{p,0}},nop,nop,nop,nop,nop]).
-define(FETCHP,    [reset,{call,{p,0}},?FETCHP_RIGHT]).
-define(FETCHB,    [reset,{call,{p,0}},{fetchp,{t,2}},{bstore,{b,2}},?FETCHB_678]).
-define(STOREB,    [reset,{call,{p,0}},{fetchp,{t,4}},{bstore,{b,4}},{fetchp,{t,678}},nop,{write,4,678},{storeb,{b,4},{t,4}}]).
-define(READ,      [reset,?CALL0,?FETCHP_RIGHT,?BSTORE_RIGHT,?FETCHB_678,nop,eof]).
-define(WRITE,     [reset,?CALL0,?FETCHP_RIGHT,?BSTORE_RIGHT,?FETCHP_678,nop,?STOREB_RIGHT,nop,nop,nop,eof]).
-define(READ_STOP, [reset,?CALL0,?FETCHP_RIGHT,?BSTORE_RIGHT,stop]).
-define(WRITE_STOP,[reset,?CALL0,?FETCHP_RIGHT,?BSTORE_RIGHT,?FETCHP_678,nop,stop]).
-define(READWRITE1,[reset,?CALL0,?FETCHP_RIGHT,?BSTORE_RIGHT,?FETCHB_678,nop,nop,nop,nop,nop]).
-define(READWRITE2,[reset,?CALL0,?FETCHP_RIGHT,?BSTORE_RIGHT,?FETCHP_678,nop,?STOREB_RIGHT,nop,nop,nop]).
-define(WRITEREAD1,[reset,?CALL0,nop,nop,nop,nop,?FETCHP_RIGHT,?BSTORE_RIGHT,?FETCHB_678,nop]).
-define(WRITEREAD2,[reset,?CALL0,?FETCHP_RIGHT,?BSTORE_RIGHT,?FETCHP_678,nop,?STOREB_RIGHT,nop,nop,nop]).


% EUNIT TESTS

step(_F18A,0) ->
   ok;

step(F18A,N) ->
   f18A:step(F18A,wait),
   step(F18A,N-1).

read() ->
   read([]).

read(L) ->
   receive
      {n001,write,X} ->
         n001 ! { n000,read,ok },
         read([X|L]);

      _else ->
         lists:reverse(L)
   end.

cucumber_test() ->
   cucumber:run(f18A_cucumber,{file,?HCCFORTH}),
   ok.

cucumber_n404_test() ->
   M    = setup("-- N404 TEST"),
   RAM  = util:read_ram("../cucumber/N404.bin"),     
   ROM  = util:read_rom("../cucumber/N404.bin"),     
   F18A = f18A:create(n001,n000,ROM,RAM),

   register(n000,spawn(fun() ->
                          L = read(),
                          M ! {rx,L}
                       end)),

   f18A:reset(F18A),
   step      (F18A,19),
   step      (F18A,13),
   step      (F18A,13),
   step      (F18A,13),
   step      (F18A,13),
   step      (F18A,13),
   f18A:stop(F18A),

   n000 ! stop,

   RX = receive
           {rx,L} ->   
              L
        end,

   trace:stop  (),
   ?assertEqual([6,8,10,12,14,16],RX),
   ?debugMsg   ("--OK").

n404_test() ->
   M    = setup("-- N404 TEST"),
   RAM  = array:from_list([16#049f3,16#00003,16#3d555,16#049f3,16#00001,16#13400,16#09703,16#04b12,16#001d5,16#3ffff,16#11403]),
   ROM  = array:new(64,[{default,16#11407}]),
   F18A = f18A:create(n001,n000,ROM,RAM),

   register(n000,spawn(fun() ->
                          L = read(),
                          M ! {rx,L}
                       end)),

   f18A:reset(F18A),
   step      (F18A,19),
   step      (F18A,13),
   step      (F18A,13),
   step      (F18A,13),
   step      (F18A,13),
   step      (F18A,13),
   f18A:stop(F18A),

   n000 ! stop,

   RX = receive
           {rx,L} ->   
              L
        end,

   trace:stop  (),
   ?assertEqual([6,8,10,12,14,16],RX),
   ?debugMsg   ("--OK").

n406_test() ->
   M    = setup("-- N406 TEST"),
   RAM  = array:from_list([16#049F3,16#00005,16#36155,16#049F3,16#00001,16#13400,16#09703,16#04B12,16#00175,16#3FFFF,16#11403]),
   ROM  = array:new(64,[{default,16#11407}]),
   F18A = f18A:create(n001,n000,ROM,RAM),

   register(n000,spawn(fun() ->
                          L = read(),
                          M ! {rx,L}
                       end)),

   f18A:reset(F18A),
   step      (F18A,19),
   step      (F18A,14),
   step      (F18A,14),
   step      (F18A,14),
   step      (F18A,14),
   step      (F18A,14),
   f18A:stop(F18A),

   n000 ! stop,

   RX = receive
           {rx,L} ->   
              L
        end,

   trace:stop(),
   ?assertEqual([15,18,21,24,27,30],RX),
   ?debugMsg   ("--OK").

go_test() ->
   M    = setup("-- GO TEST"),
   F18A = f18A:create(n001,n000,[16#2c9b2,16#2c9b2,16#2c9b2]),

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
   F18A = f18A:create(n001,n000,[16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2]),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
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

breakpoint_test() ->
   M    = setup("-- BREAKPOINT TEST"),
   F18A = f18A:create(n001,n000,[16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2]),

   f18A:breakpoint(F18A,3),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:go   (F18A,wait),
            M ! { n001,stopped }
         end),

   check(waitall([{n001,stopped}]),
         [ { ?BREAKPOINT,n001 }
         ]).

nop_test() ->
   setup("-- NOP TEST"),
   F18A = f18A:create(n001,n000,[ 16#2d555 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
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
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?NOP5,n001 }
         ]).

fetchp_test() ->
   setup("-- FETCH-P TEST"),
   F18A = f18A:create(n001,n000,[ 16#04000,16#001d5 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),

   check(trace:stop(),
         [ { ?FETCHP,n001 }
         ]).

fetchb_test() ->
   setup("-- FETCH-B TEST"),
   F18A = f18A:create(n001,n000,[ 16#04b02,16#00002,16#002a6 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
  
   check(trace:stop(),
         [ { ?FETCHB,n001 }
         ]).

storeb_test() ->
   setup("-- STORE-B TEST"),
   F18A = f18A:create(n001,n000,[ 16#04b12,16#00004,16#002a6,16#089b2,16#00000 ]),

   f18A:reset(F18A),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:step (F18A,wait),
   f18A:stop (F18A),

   check(trace:stop(),
         [ { ?STOREB,n001 }
         ]).

read_go_test() ->
   M = setup("-- READ TEST/GO"),
   util:unregister(n000),

   F18A = f18A:create(n001,n000,[16#04b02,16#001d5]),

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

   F18A = f18A:create(n001,n000,[16#04b02,16#001d5]),

   f18A:reset(F18A),

   spawn(fun() ->
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
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

   F18A = f18A:create(n001,n000,[ 16#04b12,16#001d5,16#002a6,16#089b2]),
   
   f18A:reset(F18A),
   
   register(n000,spawn(fun() ->
                          wait({ n001,write,678 }),
                          n001 ! { n000,read,ok },
                          M ! { n000,stopped }
                       end)),

   spawn(fun() ->
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

   F18A = f18A:create(n001,n000,[ 16#04b12,16#001d5,16#002a6,16#089b2 ]),
   
   register(n000,spawn(fun() ->
                          wait({ n001,write,678 }),
                          n001 ! { n000,read,ok },
                          M ! { n000,stopped }
                       end)),

   spawn(fun() ->
            f18A:reset(F18A),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            f18A:step (F18A,wait),
            M ! { n001,stopped }
         end),
         
   check(waitall([{n000,stopped},{n001,stopped}]),
         [ { ?WRITE,n001 }
         ]).

read_stop_go_test() ->
   setup("-- READ STOP TEST/GO"),
   F18A = f18A:create(n001,n000,[16#04b02,16#001d5]),

   f18A:reset(F18A),
   f18A:go   (F18A),
   f18A:stop (F18A,wait),

   check(waitall([]),
         [ { ?READ_STOP,n001 }
         ]).

read_stop_step_test() ->
   setup("-- READ STOP TEST/STEP"),
   F18A = f18A:create(n001,n000,[16#04b02,16#001d5]),

   f18A:reset(F18A),
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A),
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
                                 
   F18A = f18A:create(n001,n000,[ 16#04b12,16#001d5,16#002a6,16#089b2 ]),
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
                                 
   F18A = f18A:create(n001,n000,[ 16#04b12,16#001d5,16#002a6,16#089b2 ]),

   f18A:reset(F18A),
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
   f18A:step (F18A), 
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
      F18A = f18A:create(n001,n002,[16#04b02,16#001d5,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2 ]),
      f18A:breakpoint(F18A,3),
      f18A:reset(F18A),
      f18A:go   (F18A,wait),
      M ! { n001,stopped }
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[ 16#04b12,16#001d5,16#002a6,16#089b2,16#2c9b2 ]),
      f18A:breakpoint(F18A,4),
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
      F18A = f18A:create(n001,n002,[16#04b02,16#001d5,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2 ]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      M ! { n001,stopped }
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[ 16#04b12,16#001d5,16#002a6,16#089b2 ]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
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
      F18A = f18A:create(n001,n002,[16#2c9b2,16#04b02,16#001d5,16#2c9b2,16#2c9b2,16#2c9b2]),
      f18A:breakpoint(F18A,3),
      f18A:reset     (F18A),
      f18A:go        (F18A,wait),
      M ! { n001,stopped } 
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[ 16#04b12,16#001d5,16#002a6,16#089b2,16#2c9b2]),
      f18A:breakpoint(F18A,4),
      f18A:reset     (F18A),
      f18A:go        (F18A,wait),
      M ! { n002,stopped } 
      end),
      
   check(waitall([{n001,stopped},{n002,stopped}]),
        [ { ?WRITEREAD1,n001 },
          { ?WRITEREAD2,n002 }
        ]).

writeread_step_test() ->
   M = setup("-- WRITE-READ TEST/STEP"),

   spawn(fun() ->
      F18A = f18A:create(n001,n002,[16#2c9b2,16#04b02,16#001d5,16#2c9b2,16#2c9b2,16#2c9b2,16#2c9b2 ]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      M ! { n001,stopped } 
      end),

   spawn(fun() ->
      F18A = f18A:create(n002,n001,[ 16#04b12,16#001d5,16#002a6,16#089b2,16#2c9b2,16#2c9b2 ]),
      f18A:reset(F18A),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
      f18A:step (F18A,wait),
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

%% UTILITY FUNCTIONS

setup(TestName) ->
   log:info(?TAG,TestName),
   trace:stop (),
   trace:start(),
   self().

check(_Trace,[]) ->
   ?debugMsg("--OK"),
   ok;

check(Trace,[{Expected,ID}|T]) ->
   ?assertEqual(ok,verify:compare(Expected,trace:extract(Trace,f18A,ID),noprint)),
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

